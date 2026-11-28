"""Cards group statement pages for readers; their edges are derived from the statements, with typed witnesses."""

from __future__ import annotations

import ast
import contextlib
import copy
import hashlib
import importlib.util
import io
import itertools
import json
import os
import stat
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from collections import Counter, defaultdict
from pathlib import Path
from unittest.mock import patch

from scripts import card_moves, cards
from scripts import generate_wiki as wiki

THEOREM = {"kind": "theorem", "status": "formalized"}
DEFINITION = {"kind": "def", "status": "formalized"}
COMMIT = "c7df2d47c165e81f305e67eb4263db54d516aae9"


def af(number: int) -> str:
    return f"af_{number:024x}"


# The errors of `cards.py moves` that need the tree, which the required check (`card_moves.py check`) leaves to it:
# where each chain ends, what holds a moved or retired address, a replacement's liveness, an id two articles have, a
# replacement whose address the site cannot serve, and a checkout that is no Git one. Each is matched whole.
TREE_DEPENDENT = re.compile("|".join(rf"(?:{pattern})" for pattern in (
    r"card-moves\.jsonl: the (?:page|folder) \S+ moved but is still there",
    r"card-moves\.jsonl: \S+ moved as a (?:page|folder), and another article's (?:page|folder) now holds the "
    r"address",
    r"card-moves\.jsonl: \S+ ends at \S+, but \S+ is (?:no statement page|\S+)",
    r"card-moves\.jsonl: the folder \S+ ends at \S+, but \S+ is (?:no folder page|\S+)",
    r"card-moves\.jsonl: the retired (?:card|statement) \S+ is still the id of \S+",
    r"card-moves\.jsonl: the retired card \S+ is replaced by \S+, which is no card",
    r"card-moves\.jsonl: the retired statement \S+ is replaced by \S+, which is no live page or folder",
    r"card-moves\.jsonl: the retired (?:card|statement) \S+'s address \S+ is held by (?:an article with no id|another "
    r"article)",
    r"card-moves\.jsonl: \S+, which the ledger names, is the id of \d+ articles, .+; an id names one article",
    r"card-moves\.jsonl: the retired (?:card|statement) \S+ is replaced by \S+, whose (?:page|folder) \S+ is no "
    r"address the site serves",
    r".+ is no Git checkout: the receipt names the commit it checks")))


def tree_free(errors: list[str]) -> list[str]:
    """The errors of the moves check that need no other file than the ledger's: the required check's."""
    return [error for error in errors if not TREE_DEPENDENT.fullmatch(error)]


def required_check(root: Path, files: card_moves.Files, base: card_moves.BaseLedger | None, trees: dict) -> list[str]:
    """The required check's errors on the ledger ``files`` held to ``base``, as its command finds them:
    card_moves.check, with the live folders read from Git's tree entries (card_moves.live_folders) of a tree that Git
    writes of the roadmap below ``root`` as it is laid out, one tree per layout of its entries (``trees``)."""
    roadmap = root / card_moves.ROADMAP
    layout = tuple(sorted(path.relative_to(root).as_posix() for path in roadmap.rglob("*")
                          if path.is_symlink() or not path.is_dir()))
    if layout not in trees:
        if not (root / ".git").exists():
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "-A", "--", card_moves.ROADMAP], cwd=root, check=True)
        tree = subprocess.run(["git", "write-tree"], cwd=root, check=True, capture_output=True,
                              text=True).stdout.strip()
        trees[layout] = card_moves.live_folders(root, tree)
    return card_moves.check(files, base, trees[layout])[0]


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
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(card_moves, "ROOT", self.tmp),
                    patch.object(wiki, "VAULT", vault),
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

    def test_the_frozen_file_stays_the_base_s(self) -> None:
        published = json.dumps({"page": f"{self.g}/old", "to": f"{self.g}/a/a-main", "article_id": af(10)}) + "\n"
        later = json.dumps({"page": f"{self.g}/older", "to": f"{self.g}/a/a-lemma", "article_id": af(11)}) + "\n"
        moves = wiki.ROOT / "scripts" / cards.MOVES
        base = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(published.encode())},
                                {cards.FROZEN: published.encode()})
        moves.write_text(published)
        fragments = wiki.ROOT / cards.FRAGMENTS
        fragments.mkdir()
        (fragments / "20200101T000000Z-later.jsonl").write_text(later)
        self.assertEqual(self.run_check(base_ledger=base)[0], [])
        # A row appended to the frozen file, or one taken from it, is refused, with the fix.
        frozen = (f"{cards.MOVES} is not the base commit's; it is frozen: move the rows added to it into a fragment "
                  "with `python scripts/card_moves.py new-moves <slug> --take-appended`")
        for text in (published + later, "", published.replace(af(10), af(12))):
            with self.subTest(text=text):
                moves.write_text(text)
                self.assertIn(frozen, self.run_check(base_ledger=base)[0])
        moves.unlink()
        self.assertIn(f"{cards.MOVES}: missing; it records every address a card change retired",
                      self.run_check(dependencies=self.extraction())[0])
        # Without the strict check too, a base's ledger cannot go.
        self.assertIn(f"{cards.MOVES}: missing; it records every address a card change retired",
                      self.run_check(base_ledger=base)[0])

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
        framed = b"scripts/card-moves.jsonl\0" + str(len(ledger)).encode() + b"\0" + ledger
        self.assertEqual(made, {"schema": "atlas-card-moves/v3", "commit": self.git("rev-parse", "HEAD").strip(),
                                "ledger_sha256": hashlib.sha256(framed).hexdigest(),
                                "annotations_sha256": cards.links_digest(cards.links_snapshot()),
                                "cards": {af(1): f"{self.g}/c"}, "cards_complete": True,
                                "replacements": {af(1): {"kind": "folder", "node": f"{self.g}/c"}}})
        # Both digests are the ones the hook recomputes from the files, unparsed.
        hook = load_hook()
        self.assertEqual(made["annotations_sha256"], hook.links_digest(cards.links_dir()))
        self.assertEqual(made["ledger_sha256"], hook.ledger_digest(hook.ledger_files(wiki.ROOT)))
        # A deliberately empty ledger is a ledger with no row.
        status, errors, made = self.check(ledger="")
        self.assertEqual((status, errors, made["ledger_sha256"]),
                         (0, "", hashlib.sha256(b"scripts/card-moves.jsonl\x000\x00").hexdigest()))

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
            hook.read_receipt(self.tmp, hook.ledger_files(self.tmp))
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
                self.assertEqual(hook.valid_address(value), card_moves.valid_address(value))

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
        # The snapshot reads the ledger's order too: the move into the address comes after the retirement that frees it.
        status, errors, made = self.check(retire, move)
        self.assertEqual((status, errors), (0, ""))
        status, errors, made = self.check(move, retire)
        self.assertEqual(status, 1)
        self.assertIn(f"{cards.MOVES}:1: it builds on line 2, below it; a file's rows come in the order they happened",
                      errors)

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


class Fragments(Vault):
    """The move ledger as its frozen file and one fragment per change (docs/cards.md#move-ledger): read as one logical
    ledger, the frozen file's rows then each fragment's, by name; held to the base commit's ledger file for file; its
    new fragments found by path, never by count, and checked for independence where nothing orders them. In a real Git
    repository, where a pull request's merge commit has its base as first parent, as GitHub makes it. The base: card 1
    at g/c; the statement pages g/p, g/q, g/r and g/s; the folder g/f (50) with g/f/u."""

    git = LedgerCheck.git

    def setUp(self) -> None:
        super().setUp()
        self.g = g = "Algebra/groups"
        self.output = self.tmp / "build" / "card-moves.json"
        # The rows of pages that move are kept apart, so that two branches' annotations merge in Git.
        self.leaf(f"{g}/p.md", 20, facts=None)
        self.leaf(f"{g}/c/c-main.md", 10)
        self.leaf(f"{g}/q.md", 21, facts=None)
        self.leaf(f"{g}/c/x.md", 11)
        self.leaf(f"{g}/r.md", 22, facts=None)
        self.card(f"{g}/c", 1, 10, ["c-main", "x"])
        self.leaf(f"{g}/s.md", 24, facts=None)
        self.folder(f"{g}/f/README.md", "F", ["u.md"], {"id": af(50)})
        self.leaf(f"{g}/f/u.md", 23, facts=None)
        self.ledger_file()
        self.git("init", "-q", "-b", "main")
        self.entry_point()
        self.base = self.commit("base")
        self.at_base = copy.deepcopy(self.rows)

    def commit(self, message: str) -> str:
        self.write()
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD").strip()

    def branch(self, name: str, start: str, rows: list[dict] | None = None) -> None:
        """Check out a new branch ``name`` at ``start``, whose annotations are ``rows`` (the base's by default)."""
        self.git("checkout", "-q", "-B", name, start)
        self.rows = copy.deepcopy(self.at_base if rows is None else rows)

    def merge(self, into: str, branch: str) -> str:
        """The merge commit of ``branch`` into ``into``, whose first parent is ``into``'s tip: a pull request's merge
        ref, or a merge group's head."""
        self.git("checkout", "-q", into)
        self.git("merge", "-q", "--no-ff", "--no-edit", branch)
        return self.git("rev-parse", "HEAD").strip()

    def relocate(self, old: str, new: str) -> None:
        """Move the page ``old`` (below the roadmap) to ``new``, with its annotation."""
        (wiki.ROADMAP / new).parent.mkdir(parents=True, exist_ok=True)
        (wiki.ROADMAP / old).rename(wiki.ROADMAP / new)
        for row in self.rows:
            if row["subject"][0]["uri"] == f"../roadmap/{old}":
                row["subject"][0]["uri"] = f"../roadmap/{new}"

    def remove(self, relative: str) -> None:
        """Delete a page and its row."""
        (wiki.ROADMAP / relative).unlink()
        self.rows = [row for row in self.rows if row["subject"][0]["uri"] != f"../roadmap/{relative}"]

    def fragment(self, name: str, *rows: dict, text: str | None = None) -> str:
        folder = wiki.ROOT / cards.FRAGMENTS
        folder.mkdir(exist_ok=True)
        (folder / name).write_text(text if text is not None else "".join(json.dumps(row) + "\n" for row in rows))
        return f"{cards.FRAGMENTS}/{name}"

    def moves(self, *arguments: str) -> tuple[int, str]:
        """The moves command on the checkout as it is: its exit status and its errors. The required check, run as itself
        on the same checkout with the same arguments (check), gives the same errors but those that need the tree
        (tree_free), in the same order, and fails exactly when it gives one."""
        errors = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            status = cards.run(["moves", str(self.output), *arguments])
        if status != 2:
            expected = tree_free([line.removeprefix("error: ") for line in errors.getvalue().splitlines()])
            required, said = self.check(*arguments)
            self.assertEqual(([line.removeprefix("error: ") for line in said.splitlines()], required),
                             (expected, 1 if expected else 0), errors.getvalue())
        return status, errors.getvalue()

    def check(self, *arguments: str) -> tuple[int, str]:
        """`python scripts/card_moves.py check …`, the required check, run as itself from the checkout (entry_point),
        with no root injected: its exit status and its errors."""
        self.entry_point()
        result = subprocess.run([sys.executable, "scripts/card_moves.py", "check", *arguments], cwd=self.tmp,
                                capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        return result.returncode, result.stderr

    def snapshot(self, **options) -> list[str]:
        """check_moves on the checkout's files as they are."""
        annotations = cards.read_annotations()
        return cards.check_moves(annotations, cards.card_folders(annotations), **options)

    def strict(self, base: str) -> list[str]:
        """The moves part of the strict check of the checkout against ``base``, its ledger, annotations and renames
        extracted as the card job extracts them."""
        work = Path(tempfile.mkdtemp(dir=self.tmp.parent))
        self.addCleanup(shutil.rmtree, work)
        (work / "scripts").mkdir()
        (work / "scripts" / cards.MOVES).write_text(self.git("show", f"{base}:scripts/{cards.MOVES}"))
        if self.git("ls-tree", base, "--", cards.FRAGMENTS):
            archive = subprocess.run(["git", "-C", str(self.tmp), "archive", base, cards.FRAGMENTS], check=True,
                                     capture_output=True).stdout
            subprocess.run(["tar", "-x", "-C", str(work)], input=archive, check=True)
        (work / "links").mkdir()
        (work / "links" / "Algebra.jsonl").write_text(self.git("show", f"{base}:blueprint/links/Algebra.jsonl"))
        known, problems = card_moves.base_from_folder(work / "scripts")
        self.assertEqual(problems, [])
        renames = work / "renames.tsv"
        renames.write_text(self.git("-c", "diff.renameLimit=0", "diff", "--name-status", "-M", base, "HEAD", "--",
                                    "blueprint/roadmap"))
        return self.snapshot(base=known, base_annotations=cards.read_links(work / "links"),
                             renames=cards.read_renames(renames))

    def resolution(self) -> dict:
        """What the site keeps of the checkout's ledger: the receipt's cards and replacements, and the hook's
        resolution of every old address (history), from the files as they are."""
        status, errors = self.moves()
        self.assertEqual((status, errors), (0, ""))
        made = json.loads(self.output.read_text())
        hook = load_hook()
        pages = hook.Pages(hook.read_index(site_index(hook)))
        files = hook.ledger_files(self.tmp)
        ledger = hook.read_ledger([(path, data.decode()) for path, data in files])
        replacements = {article: (found["kind"], found["node"]) for article, found in made["replacements"].items()}
        return {"cards": made["cards"], "replacements": made["replacements"],
                "history": hook.history(ledger, pages, replacements)}

    def test_the_logical_ledger_is_the_frozen_file_then_each_fragment_by_name(self) -> None:
        g = self.g
        (wiki.ROOT / "scripts" / cards.MOVES).write_text(json.dumps(
            {"page": f"{g}/old-p", "to": f"{g}/p", "article_id": af(20)}) + "\n")
        # Made later, sorted earlier: the order is the names', and a file with no final newline joins no rows.
        self.fragment("20260102T000000Z-b.jsonl", {"page": f"{g}/old-q", "to": f"{g}/q", "article_id": af(21)})
        self.fragment("20260101T000000Z-a.jsonl",
                      text=json.dumps({"page": f"{g}/old-r", "to": f"{g}/r", "article_id": af(22)}) + "\n\n"
                      + json.dumps({"page": f"{g}/old-s", "to": f"{g}/s", "article_id": af(24)}))
        files, problems = card_moves.read_ledger(wiki.ROOT / "scripts")
        self.assertEqual(problems, [])
        self.assertEqual([(path, number) for path, number, _ in card_moves.ledger_rows(files)], [
            ("scripts/card-moves.jsonl", 1), ("scripts/card-moves.d/20260101T000000Z-a.jsonl", 1),
            ("scripts/card-moves.d/20260101T000000Z-a.jsonl", 3), ("scripts/card-moves.d/20260102T000000Z-b.jsonl", 1)])
        self.assertEqual(self.snapshot(), [])
        # A row of a fragment is named by its file and line.
        self.fragment("20260103T000000Z-c.jsonl", text="\n{not json\n")
        self.assertEqual(self.snapshot(), ["scripts/card-moves.d/20260103T000000Z-c.jsonl:2: not JSON"])
        # A missing or empty folder holds no fragment.
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        self.assertEqual(card_moves.read_ledger(wiki.ROOT / "scripts")[0][1:], [])
        (wiki.ROOT / cards.FRAGMENTS).mkdir()
        self.assertEqual(card_moves.read_ledger(wiki.ROOT / "scripts"), (
            [("scripts/card-moves.jsonl", (wiki.ROOT / "scripts" / cards.MOVES).read_bytes())], []))

    def test_every_entry_of_the_folder_of_fragments_is_a_fragment(self) -> None:
        folder = wiki.ROOT / cards.FRAGMENTS
        folder.mkdir()
        row = json.dumps({"page": f"{self.g}/old-p", "to": f"{self.g}/p", "article_id": af(20)}) + "\n"
        (self.tmp / "elsewhere.jsonl").write_text(row)
        cases = {
            "notes.txt": (lambda path: path.write_text(row), "not a fragment; a fragment is a file named "
                                                            "<YYYYMMDDTHHMMSSZ>-<slug>.jsonl"),
            ".gitkeep": (lambda path: path.write_text(""), "not a fragment"),
            "20260101T000000Z-Upper.jsonl": (lambda path: path.write_text(row), "not a fragment"),
            "20260101T000000Z-x.json": (lambda path: path.write_text(row), "not a fragment"),
            "20261301T000000Z-month.jsonl": (lambda path: path.write_text(row),
                                             "not a fragment; 20261301T000000Z is no UTC time"),
            "20260101T250000Z-hour.jsonl": (lambda path: path.write_text(row), "20260101T250000Z is no UTC time"),
            "20260101T000000Z-link.jsonl": (lambda path: path.symlink_to(self.tmp / "elsewhere.jsonl"),
                                            "no regular file"),
            "20260101T000000Z-folder.jsonl": (lambda path: path.mkdir(), "no regular file"),
            "20260101T000000Z-empty.jsonl": (lambda path: path.write_text(""), "no row; a fragment holds at least one"),
            "20260101T000000Z-blank.jsonl": (lambda path: path.write_text("\n  \n"), "no row"),
            "20260101T000000Z-latin.jsonl": (lambda path: path.write_bytes(b'{"page": "\xe9"}\n'), "not UTF-8"),
        }
        hook = load_hook()
        for name, (make, problem) in cases.items():
            with self.subTest(name=name):
                make(folder / name)
                files, problems = card_moves.read_ledger(wiki.ROOT / "scripts")
                self.assertEqual(len(problems), 1, problems)
                self.assertTrue(problems[0].startswith(f"scripts/card-moves.d/{name}: ") and problem in problems[0],
                                problems)
                # The entry is left out, and named; the check refuses the ledger, and the hook keeps nothing.
                self.assertEqual(len(files), 1)
                self.assertIn(problems[0], self.snapshot())
                with self.assertRaises(hook.CardDataError) as refused:
                    hook.ledger_files(self.tmp)
                self.assertEqual(str(refused.exception), problems[0])
                status, errors = self.moves()
                self.assertEqual((status, self.output.exists()), (1, False))
                self.assertIn(problems[0], errors)
                target = folder / name
                shutil.rmtree(target) if target.is_dir() and not target.is_symlink() else target.unlink()
        # The folder itself is a folder.
        folder.rmdir()
        folder.write_text(row)
        self.assertEqual(card_moves.read_ledger(wiki.ROOT / "scripts")[1], ["scripts/card-moves.d is no folder"])

    def test_a_linked_folder_of_fragments_or_fragment_is_refused_by_every_reader(self) -> None:
        # scripts/card-moves.d a link to a folder outside the checkout, holding a fragment that the ledger would take:
        # the scripts' reader, the hook's, the moves command, the card check and the printed ledger refuse it, by the
        # same words, and no receipt is written. Committed so, Git keeps the link as a link: the reader of a commit's
        # trees refuses it too, and `moves --base` on that commit; and so a linked fragment, and a folder named as one.
        g = self.g
        hook = load_hook()
        outside = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, outside)
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.write()
        (outside / "20260101T000000Z-a.jsonl").write_text(
            json.dumps({"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)}) + "\n")
        folder = wiki.ROOT / cards.FRAGMENTS
        folder.symlink_to(outside)
        problem = "scripts/card-moves.d is no folder"
        files, problems = card_moves.read_ledger(wiki.ROOT / "scripts")
        self.assertEqual(([path for path, _ in files], problems), ([cards.FROZEN], [problem]))
        with self.assertRaises(hook.CardDataError) as refused:
            hook.ledger_files(self.tmp)
        self.assertEqual(str(refused.exception), problem)
        self.assertIn(problem, self.snapshot())
        status, errors = self.moves()
        self.assertEqual((status, self.output.exists()), (1, False))
        self.assertIn(problem, errors)
        printed = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(printed):
            self.assertEqual(card_moves.main(["--repo", str(self.tmp)]), 1)
            self.assertEqual(cards.run(["check"]), 1)
        self.assertIn(f"error: {problem}", printed.getvalue())
        self.assertEqual(printed.getvalue().count(f"error: {problem}"), 2)
        # Committed as a link.
        linked = self.commit("a linked folder of fragments")
        self.assertEqual(self.git("ls-tree", linked, "--", cards.FRAGMENTS).split()[0], "120000")
        self.assertEqual(card_moves.ledger_blobs(linked, self.tmp)[1], [problem])
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(card_moves.main(["--repo", str(self.tmp), linked]), 1)
        folder.unlink()
        folder.mkdir()
        (folder / "20260101T000000Z-a.jsonl").write_bytes((outside / "20260101T000000Z-a.jsonl").read_bytes())
        self.commit("a real folder of fragments")
        status, errors = self.moves("--base", linked)
        self.assertEqual(status, 1)
        self.assertIn(f"the base commit's {problem}", errors)
        # A linked fragment, and a folder named as a fragment, committed: no regular file, read from the trees.
        (folder / "20260102T000000Z-b.jsonl").symlink_to(outside / "20260101T000000Z-a.jsonl")
        (folder / "20260103T000000Z-c.jsonl").mkdir()
        (folder / "20260103T000000Z-c.jsonl" / "x").write_text("x\n")
        entries = self.commit("a linked fragment and a folder")
        self.assertEqual(card_moves.ledger_blobs(entries, self.tmp)[1],
                         ["scripts/card-moves.d/20260102T000000Z-b.jsonl: no regular file",
                          "scripts/card-moves.d/20260103T000000Z-c.jsonl: no regular file"])

    def test_the_hook_reads_the_ledger_as_the_scripts_do(self) -> None:
        # Parity of the two readers, on valid layouts: the same files, bytes and rows, in the same order.
        hook = load_hook()
        g = self.g
        layouts = [
            {},
            {"20260101T000000Z-a.jsonl": json.dumps({"page": f"{g}/o", "to": f"{g}/p", "article_id": af(20)})},
            {"20260102T000000Z-b.jsonl": "\n" + json.dumps({"page": f"{g}/o2", "to": f"{g}/q", "article_id": af(21)}),
             "20260101T235959Z-z.jsonl": json.dumps({"statement": af(30), "page": f"{g}/gone", "replaced_by": af(20)})
             + "\n"},
        ]
        for layout in layouts:
            with self.subTest(layout=sorted(layout)):
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
                for name, text in layout.items():
                    self.fragment(name, text=text)
                files, problems = card_moves.read_ledger(wiki.ROOT / "scripts")
                self.assertEqual((hook.ledger_files(self.tmp), problems), (files, []))
                self.assertEqual(hook.ledger_digest(files), card_moves.digest(files))
                rows = [json.loads(line) for _, _, line in card_moves.ledger_rows(files)]
                self.assertEqual(len(hook.read_ledger([(path, data.decode()) for path, data in files]).rows),
                                 len(rows))
        # A frozen file that is no regular file is refused alike; a missing one is no empty ledger for either.
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        frozen.unlink()
        with self.assertRaises(FileNotFoundError):
            card_moves.read_ledger(wiki.ROOT / "scripts")
        with self.assertRaises(hook.CardDataError):
            hook.ledger_files(self.tmp)
        frozen.symlink_to(self.tmp / "elsewhere")
        (self.tmp / "elsewhere").write_text("")
        with self.assertRaises(hook.CardDataError) as refused:
            hook.ledger_files(self.tmp)
        self.assertEqual(card_moves.read_ledger(wiki.ROOT / "scripts")[1], [str(refused.exception)])

    def test_the_frozen_file_and_the_base_s_fragments_stay_as_they_are(self) -> None:
        # The base has a fragment, a: deleting it, renaming it, editing it, making it a link or appending to the
        # frozen file each fails the required step against that base; a new fragment beside it does not.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        a = self.fragment("20260101T000000Z-a.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        base = self.commit("a")
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        self.fragment("20260102T000000Z-b.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        self.commit("b")
        self.assertEqual(self.moves("--base", base), (0, ""))
        bytes_of_a = (self.tmp / a).read_bytes()
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        cases = {
            "deleted": (lambda: (self.tmp / a).unlink(),
                        f"{a}, a fragment of the base commit, is gone; a published fragment is never deleted, renamed "
                        "or made another kind of file"),
            "renamed": (lambda: (self.tmp / a).rename(self.tmp / a.replace("-a.jsonl", "-renamed.jsonl")),
                        f"{a}, a fragment of the base commit, is gone"),
            "edited": (lambda: (self.tmp / a).write_bytes(bytes_of_a.replace(b'", "', b'","')),
                       f"{a}, a fragment of the base commit, changed; a published fragment is never edited"),
            "a link": (lambda: ((self.tmp / "kept.jsonl").write_bytes(bytes_of_a), (self.tmp / a).unlink(),
                                (self.tmp / a).symlink_to(self.tmp / "kept.jsonl")),
                       f"{a}, a fragment of the base commit, is gone"),
            "appended": (lambda: frozen.write_text(json.dumps({"page": f"{g}/old", "to": f"{g}/r",
                                                               "article_id": af(22)}) + "\n"),
                         f"{cards.MOVES} is not the base commit's; it is frozen: move the rows added to it into a "
                         "fragment with `python scripts/card_moves.py new-moves <slug> --take-appended`"),
        }
        for name, (change, message) in cases.items():
            with self.subTest(name=name):
                change()
                status, errors = self.moves("--base", base)
                self.assertEqual(status, 1)
                self.assertIn(message, errors)
                # The snapshot alone does not see it: the comparison with the base does.
                self.assertNotIn(message, "\n".join(self.snapshot()))
                self.git("checkout", "-q", "--", ".")
                self.git("clean", "-q", "-f", "-d", "--", "scripts")
                (self.tmp / "kept.jsonl").unlink(missing_ok=True)
        self.assertEqual(self.moves("--base", base), (0, ""))

    def test_a_base_whose_ledger_cannot_be_read_is_no_empty_one(self) -> None:
        status, errors = self.moves("--base", "f" * 40)
        self.assertEqual(status, 1)
        self.assertIn(f"--base {'f' * 40}: no commit Git can read here", errors)
        self.git("rm", "-q", f"scripts/{cards.MOVES}")
        self.git("commit", "-q", "-m", "no ledger")
        old = self.git("rev-parse", "HEAD").strip()
        self.git("checkout", "-q", "main~1", "--", f"scripts/{cards.MOVES}")
        self.commit("the ledger again")
        status, errors = self.moves("--base", old)
        self.assertEqual(status, 1)
        self.assertIn(f"--base {old}: the commit has no scripts/card-moves.jsonl as a regular file", errors)
        work = self.tmp.parent / f"{self.tmp.name}-base"
        work.mkdir()
        self.addCleanup(shutil.rmtree, work)
        self.assertEqual(card_moves.base_from_folder(work)[0], None)
        self.assertIn("the base commit's move ledger cannot be read", card_moves.base_from_folder(work)[1][0])

    def test_new_fragments_are_found_by_path_never_by_count(self) -> None:
        # The base has a, stamped second; the change adds b, stamped first: the logical ledger [frozen, b, a] does not
        # extend the base's [frozen, a], and b's rows, not the last row, are the ones replayed from the base.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.fragment("20260102T000000Z-a.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        base = self.commit("a")
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        self.fragment("20260101T000000Z-b.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        self.commit("b")
        self.assertEqual(self.moves("--base", base), (0, ""))
        self.assertEqual(self.strict(base), [])
        # Against the base before a, both are new, and both moves since are accounted for.
        self.assertEqual(self.moves("--base", self.base), (0, ""))
        self.assertEqual(self.strict(self.base), [])
        # Without b's row the move since the base is missing, whatever the ledger's length: the card check says so; the
        # required step holds the ledger to the base's and no more.
        self.fragment("20260101T000000Z-b.jsonl", {"page": f"{g}/r-old", "to": f"{g}/r", "article_id": af(22)})
        self.commit("b without its row")
        self.assertIn(f"{cards.MOVES}: {g}/q is now {g}/f/q, and no row leads there", self.strict(base))
        self.assertEqual(self.moves("--base", base), (0, ""))

    def test_the_required_step_leaves_the_moves_since_the_base_to_the_card_check(self) -> None:
        # A pull request moves q and deletes r, with no ledger row. The required step (moves --base) checks the ledger's
        # integrity and passes; the card check (check --base-ledger --base-links --renames) reconciles the changes since
        # the base and fails, with its usual errors.
        g = self.g
        self.branch("pr", self.base)
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        self.remove(f"{g}/r.md")
        self.commit("move q and delete r, with no row")
        rows = self.rows
        self.branch("main", self.base)
        self.commit("main moves on")
        self.merge("main", "pr")
        self.assertEqual(self.moves("--base", self.git("rev-parse", "HEAD^1").strip()), (0, ""))
        errors = self.strict(self.git("rev-parse", "HEAD^1").strip())
        self.assertIn(f"{cards.MOVES}: {g}/q is now {g}/f/q, and no row leads there", errors)
        self.assertIn(f"{cards.MOVES}: {g}/r ({af(22)}) is gone, and no row moves it; an article keeps its address or "
                      "moves with its row", errors)
        # With their rows in a fragment of its own, both pass.
        self.branch("pr", "pr", rows)
        self.fragment("20260101T000000Z-pr.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)},
                      {"statement": af(22), "page": f"{g}/r", "replaced_by": af(24)})
        self.commit("the rows")
        self.git("checkout", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^1")
        self.merge("main", "pr")
        self.assertEqual(self.moves("--base", self.git("rev-parse", "HEAD^1").strip()), (0, ""))
        self.assertEqual(self.strict(self.git("rev-parse", "HEAD^1").strip()), [])

    def test_a_statement_s_address_goes_to_a_folder_only_after_its_retirement(self) -> None:
        # The statement s (24) is retired for the folder f (50), which then moves to s's address with its page u: both
        # the required step (moves --base) and the card check pass it. With the folder's move first, while the address
        # was still the statement's, both refuse it, for the same reason.
        g = self.g
        self.branch("pr", self.base)
        self.remove(f"{g}/s.md")
        (wiki.ROADMAP / f"{g}/f").rename(wiki.ROADMAP / f"{g}/s")
        for row in self.rows:
            row["subject"][0]["uri"] = row["subject"][0]["uri"].replace(f"/{g}/f/", f"/{g}/s/")
        retire = {"statement": af(24), "page": f"{g}/s", "replaced_by": af(50)}
        moves = [{"folder": f"{g}/f", "to": f"{g}/s", "article_id": af(50)},
                 {"page": f"{g}/f/u", "to": f"{g}/s/u", "article_id": af(23)}]
        path = self.fragment("20260101T000000Z-handoff.jsonl", retire, *moves)
        self.commit("hand s's address to f")
        rows = self.rows
        self.merge("main", "pr")
        base = self.git("rev-parse", "HEAD^1").strip()
        self.assertEqual(self.moves("--base", base), (0, ""))
        self.assertEqual(self.strict(base), [])
        self.git("checkout", "-q", "pr")
        self.rows = rows
        self.fragment("20260101T000000Z-handoff.jsonl", *moves, retire)
        self.commit("the move first")
        self.git("checkout", "-q", "main")
        self.git("reset", "-q", "--hard", base)
        self.merge("main", "pr")
        reason = f"{path}:1: it builds on line 3, below it; a file's rows come in the order they happened"
        status, errors = self.moves("--base", base)
        self.assertEqual(status, 1)
        self.assertIn(reason, errors)
        self.assertIn(reason, self.strict(base))

    def test_an_article_moves_into_an_address_once(self) -> None:
        # The base's frozen file moves p (20) from older to p. A later fragment moves it into p again, from second-old,
        # while p and its row stay as they are: two branches of one history. The snapshot, the required step (which
        # writes no receipt) and the card check refuse it, naming both rows; and so for the two rows in one new
        # fragment, and for a folder, f (50). In two new fragments the guard declines the pair too, after the refusal.
        g = self.g
        frozen = wiki.ROOT / "scripts" / cards.MOVES

        def refusal(at: str, before: str, kind: str, old: str, earlier: str, to: str, number: int) -> str:
            return (f"{at}: {af(number)} moves into {g}/{to} a second time, from {g}/{old}, after {before} moved it "
                    f"there from {g}/{earlier}; an article moves into an address once, or its history would branch")

        def refused_everywhere(base: str, message: str) -> None:
            self.commit("the second move")
            self.assertIn(message, self.snapshot())
            self.output.unlink(missing_ok=True)
            status, errors = self.moves("--base", base)
            self.assertEqual((status, self.output.exists()), (1, False))
            self.assertIn(message, errors)
            self.assertIn(message, self.strict(base))

        for kind, number, to, older, second_old in (("page", 20, "p", "older", "second-old"),
                                                   ("folder", 50, "f", "f-old", "f-older")):
            with self.subTest(kind=kind):
                first = {kind: f"{g}/{older}", "to": f"{g}/{to}", "article_id": af(number)}
                second = {kind: f"{g}/{second_old}", "to": f"{g}/{to}", "article_id": af(number)}
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
                # Published and new.
                frozen.write_text(json.dumps(first) + "\n")
                published = self.commit(f"{kind} moved from {older}")
                self.assertEqual(self.moves("--base", published), (0, ""))
                path = self.fragment("20260101T000000Z-again.jsonl", second)
                refused_everywhere(published, refusal(f"{path}:1", f"{cards.MOVES}:1", kind, second_old, older, to,
                                                      number))
                # Both rows in one new fragment.
                frozen.write_text("")
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
                empty = self.commit("an empty ledger")
                one = self.fragment("20260101T000000Z-both.jsonl", first, second)
                refused_everywhere(empty, refusal(f"{one}:2", f"{one}:1", kind, second_old, older, to, number))
                # In two new fragments: the refusal, then the guard's.
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
                early = self.fragment("20260101T000000Z-first.jsonl", first)
                late = self.fragment("20260102T000000Z-second.jsonl", second)
                self.commit("the two moves apart")
                errors = self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}))
                message = refusal(f"{late}:1", f"{early}:1", kind, second_old, older, to, number)
                guard = next(at for at, error in enumerate(errors) if "both new, touch" in error)
                self.assertLess(errors.index(message), guard)
                status, errors = self.moves("--base", empty)
                self.assertEqual((status, self.output.exists()), (1, False))
                self.assertIn(message, errors)

    def test_what_converges_lawfully_still_passes(self) -> None:
        # One article moving on from where it moved; two retired statements naming one successor; and a page and a
        # folder of one name, handed over by a retirement: none is two moves of one article into one address.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p2.md")
        self.remove(f"{g}/q.md")
        self.remove(f"{g}/r.md")
        self.write()
        self.fragment("20260101T000000Z-lawful.jsonl", {"page": f"{g}/older", "to": f"{g}/p", "article_id": af(20)},
                      {"page": f"{g}/p", "to": f"{g}/f/p2", "article_id": af(20)},
                      {"statement": af(21), "page": f"{g}/q", "replaced_by": af(24)},
                      {"statement": af(22), "page": f"{g}/r", "replaced_by": af(24)})
        self.assertEqual(self.snapshot(), [])
        self.assertEqual(self.moves(), (0, ""))
        # A page row into s, the statement there retired for the folder f, and f moving into s with u: a page and a
        # folder each arrive at s once.
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        self.git("checkout", "-q", "--", ".")
        self.git("clean", "-q", "-f", "-d", "--", "blueprint", "scripts")
        self.rows = copy.deepcopy(self.at_base)
        self.remove(f"{g}/s.md")
        (wiki.ROADMAP / f"{g}/f").rename(wiki.ROADMAP / f"{g}/s")
        for row in self.rows:
            row["subject"][0]["uri"] = row["subject"][0]["uri"].replace(f"/{g}/f/", f"/{g}/s/")
        self.write()
        self.fragment("20260101T000000Z-handoff.jsonl", {"page": f"{g}/s-old", "to": f"{g}/s", "article_id": af(24)},
                      {"statement": af(24), "page": f"{g}/s", "replaced_by": af(50)},
                      {"folder": f"{g}/f", "to": f"{g}/s", "article_id": af(50)},
                      {"page": f"{g}/f/u", "to": f"{g}/s/u", "article_id": af(23)})
        self.assertEqual(self.snapshot(), [])

    def test_a_stamp_is_ascii_digits(self) -> None:
        # Other digits would sort after every ASCII stamp, so that no restamp could ever put a fragment after it: the
        # reader, the moves check, the card check and the hook all refuse such a name before it is published.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.write()
        row = {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)}
        hook = load_hook()
        for name in ("\uff12\uff10\uff12\uff160101T000000Z-first.jsonl", "20260101T\uff10\uff10\uff10000Z-first.jsonl",
                     "2026010\u0661T000000Z-first.jsonl", "20260101T00000\u0e50Z-first.jsonl"):
            with self.subTest(name=name.encode("unicode_escape").decode()):
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
                path = self.fragment(name, row)
                problem = f"{path}: not a fragment; a fragment is a file named <YYYYMMDDTHHMMSSZ>-<slug>.jsonl"
                self.assertEqual(card_moves.name_problem(name), problem.split(": ", 1)[1])
                self.assertEqual(card_moves.read_ledger(wiki.ROOT / "scripts")[1], [problem])
                self.assertIn(problem, self.snapshot())
                self.assertIn(problem, cards.check()[0])
                status, errors = self.moves()
                self.assertEqual((status, self.output.exists()), (1, False))
                self.assertIn(problem, errors)
                with self.assertRaises(hook.CardDataError) as refused:
                    hook.ledger_files(self.tmp)
                self.assertEqual(str(refused.exception), problem)

    def test_a_new_fragment_is_stamped_no_later_than_the_check_s_clock(self) -> None:
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        path = self.fragment("20260101T020000Z-p.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        self.commit("p")
        known = card_moves.base_at(self.base, wiki.ROOT)[0]
        with patch.object(card_moves, "utc_now", return_value=datetime(2026, 1, 1, 1, 0, tzinfo=timezone.utc)):
            self.assertEqual(self.snapshot(base=known), [])
        with patch.object(card_moves, "utc_now", return_value=datetime(2026, 1, 1, 0, 59, 59, tzinfo=timezone.utc)):
            self.assertEqual(self.snapshot(base=known), [
                f"{path} is stamped 2026-01-01 02:00:00 UTC, ahead of this check's clock, 2026-01-01 00:59:59 UTC; a "
                f"stamp is the UTC time its fragment was made: restamp it with `python scripts/card_moves.py new-moves "
                f"--restamp {path}`"])
            # A fragment the base has is published history, whatever its stamp.
            self.assertEqual(self.snapshot(base=card_moves.base_at("HEAD", wiki.ROOT)[0]), [])

    def test_a_row_comes_after_the_rows_it_builds_on(self) -> None:
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p2.md")
        hop = {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)}
        on = {"page": f"{g}/f/p", "to": f"{g}/f/p2", "article_id": af(20)}
        self.write()
        # In one file: the authored order is the history's.
        self.fragment("20260101T000000Z-p.jsonl", hop, on)
        self.assertEqual(self.snapshot(), [])
        self.fragment("20260101T000000Z-p.jsonl", on, hop)
        self.assertEqual(self.snapshot(), ["scripts/card-moves.d/20260101T000000Z-p.jsonl:1: it builds on line 2, "
                                           "below it; a file's rows come in the order they happened"])
        # Across fragments, without a base: both fixes are named.
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        early = self.fragment("20260101T000000Z-on.jsonl", on)
        late = self.fragment("20260102T000000Z-hop.jsonl", hop)
        self.assertEqual(self.snapshot(), [
            f"{early}:1: it builds on {late}, which sorts after it: restamp yours with `python "
            f"scripts/card_moves.py new-moves --restamp {early}`; if {late} is new too, put the rows of the two in one "
            "fragment, in the order they happened"])
        # With the base: past a fragment the base has, a restamp; with two new ones, one fragment.
        published = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b""), late: card_moves.blob_id(
            (self.tmp / late).read_bytes())})
        errors = self.snapshot(base=published)
        self.assertIn(f"{early}:1: it builds on {late}, which sorts after it: restamp yours with `python "
                      f"scripts/card_moves.py new-moves --restamp {early}`", errors)
        self.assertFalse(any("one fragment" in error for error in errors), errors)
        errors = self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}))
        self.assertIn(f"{early}:1: it builds on {late}, which sorts after it: put the rows of the two in one fragment, "
                      "in the order they happened", errors)
        self.assertFalse(any("restamp" in error for error in errors if error.startswith(early)), errors)
        # Replayed from the base, a row of a new fragment that fails says which fragment sorting after its own names
        # what it names, and how to order the two: both new here, so one fragment.
        base_annotations = cards.read_annotations()
        for row in base_annotations.values():
            if row.get("id") == af(20):
                row["subject"] = [{"type": "generic", "uri": f"../roadmap/{g}/p.md"}]
        moved = {page: row for page, row in base_annotations.items() if row.get("id") != af(20)}
        moved[(wiki.ROADMAP / f"{g}/p.md").resolve()] = {"id": af(20)}
        errors = self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}),
                               base_annotations=moved, renames=[])
        self.assertIn(f"{early}:1: no page is at {g}/f/p when this row moves it; it builds on {late}, which sorts "
                      "after it: put the rows of the two in one fragment, in the order they happened", errors)
        # Restamped after it, the ledger is in order.
        (self.tmp / early).rename(self.tmp / early.replace("20260101T000000Z", "20260103T000000Z"))
        self.assertEqual(self.snapshot(), [])

    def test_the_guard_declines_interacting_fragments_where_no_name_orders_them(self) -> None:
        g = self.g
        base = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")})
        # Two moves under one live folder only read it: they are independent.
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        self.write()
        one = self.fragment("20260101T000000Z-p.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        two = self.fragment("20260102T000000Z-q.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        self.assertEqual(self.snapshot(base=base), [])
        # One fragment moves the folder f, the other a page into it: the first writes what the second reads.
        self.relocate(f"{g}/r.md", f"{g}/f/r.md")
        (wiki.ROADMAP / f"{g}/f").rename(wiki.ROADMAP / f"{g}/f2")
        for row in self.rows:
            row["subject"][0]["uri"] = row["subject"][0]["uri"].replace(f"{g}/f/", f"{g}/f2/")
        self.write()
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        one = self.fragment("20260101T000000Z-f.jsonl", {"folder": f"{g}/f", "to": f"{g}/f2", "article_id": af(50)},
                            {"page": f"{g}/f/u", "to": f"{g}/f2/u", "article_id": af(23)},
                            {"page": f"{g}/f/p", "to": f"{g}/f2/p", "article_id": af(20)},
                            {"page": f"{g}/f/q", "to": f"{g}/f2/q", "article_id": af(21)},
                            {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)},
                            {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        self.fragment("20260101T000000Z-f.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)},
                      {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)},
                      {"folder": f"{g}/f", "to": f"{g}/f2", "article_id": af(50)},
                      {"page": f"{g}/f/u", "to": f"{g}/f2/u", "article_id": af(23)},
                      {"page": f"{g}/f/p", "to": f"{g}/f2/p", "article_id": af(20)},
                      {"page": f"{g}/f/q", "to": f"{g}/f2/q", "article_id": af(21)})
        two = self.fragment("20260102T000000Z-r.jsonl", {"page": f"{g}/r", "to": f"{g}/f2/r", "article_id": af(22)})
        self.assertEqual(self.snapshot(), [])
        together = (f"{one} and {two}, both new, touch the address {g}/f2: put their rows in one fragment, in the "
                    "order they happened, or land one change first and check the other again with it in its base")
        self.assertEqual(self.snapshot(base=base), [together])
        # The same pair, the first published and sorting after the second: a restamp of the second.
        published = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b""),
                                      one: card_moves.blob_id((self.tmp / one).read_bytes())})
        late = (self.tmp / one).rename(self.tmp / one.replace("20260101T000000Z", "20260103T000000Z"))
        published = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b""),
                                      late.relative_to(self.tmp).as_posix(): card_moves.blob_id(late.read_bytes())})
        crossing = (f"{two} sorts before {late.relative_to(self.tmp).as_posix()}, which the base commit has, and both "
                    f"touch the address {g}/f2: restamp it with `python scripts/card_moves.py new-moves --restamp "
                    f"{two}`, so that it sorts after it")
        self.assertIn(crossing, self.snapshot(base=published))
        # Restamped past it, the new fragment is checked in order.
        (self.tmp / two).rename(self.tmp / two.replace("20260102T000000Z", "20260104T000000Z"))
        self.assertEqual(self.snapshot(base=published), [])

    def test_a_folder_replay_may_find_gone_is_written_by_every_move_out_of_it(self) -> None:
        # f is gone once both its pages leave it: each move out of it may make the replay lead f where g leads, so
        # two new fragments that each empty part of it interact; a move into a live folder never does.
        g = self.g
        self.folder(f"{g}/h/README.md", "H", ["v.md", "w.md"], {"id": af(51)})
        self.leaf(f"{g}/h/v.md", 25, facts=None)
        self.leaf(f"{g}/h/w.md", 26, facts=None)
        self.write()
        self.relocate(f"{g}/h/v.md", f"{g}/v.md")
        self.relocate(f"{g}/h/w.md", f"{g}/w.md")
        self.remove(f"{g}/h/README.md")
        self.write()
        rows = card_moves.LedgerRow("x", 1, {"page": f"{g}/h/v", "to": f"{g}/v", "article_id": af(25)})
        stable = card_moves.stable_folders([rows], cards.LiveFolders())
        self.assertEqual(card_moves.footprint([rows], stable),
                         ({f"address:{g}/h/v", f"address:{g}/v", f"id:{af(25)}", f"address:{g}/h"},
                          {f"address:{g}/h", f"address:{g}", "address:Algebra"}))
        one = self.fragment("20260101T000000Z-v.jsonl", {"page": f"{g}/h/v", "to": f"{g}/v", "article_id": af(25)})
        two = self.fragment("20260102T000000Z-w.jsonl", {"page": f"{g}/h/w", "to": f"{g}/w", "article_id": af(26)})
        self.assertIn(f"{one} and {two}, both new, touch the address {g}/h: put their rows in one fragment",
                      "\n".join(self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}))))
        # A live folder a folder row moves into is no stable one: undoing the row takes it out of the replay.
        folder_row = card_moves.LedgerRow("y", 1, {"folder": f"{g}/c-old", "to": f"{g}/c", "article_id": af(1)})
        page_row = card_moves.LedgerRow("z", 1, {"page": f"{g}/c/x-old", "to": f"{g}/c/x", "article_id": af(11)})
        stable = card_moves.stable_folders([folder_row, page_row], cards.LiveFolders())
        self.assertFalse(stable(f"{g}/c"))
        self.assertIn(f"address:{g}/c", card_moves.footprint([page_row], stable)[0])

    def test_a_crossing_resolves_alike_in_one_fragment_and_is_declined_in_two(self) -> None:
        # P moves the statement 11 out of T/old into T/live; R retires card 7 at T/old for card 1 at T/live. No
        # literal address or id is shared; the replay's fallback for the gone T/old is. As two new fragments the
        # guard declines them; in one fragment, either authored order is checked and resolves T/old to T/live.
        g = self.g
        self.leaf(f"{g}/c/u.md", 12, facts=None)
        self.write()
        p = {"page": f"{g}/old/u", "to": f"{g}/c/u", "article_id": af(12)}
        r = {"card": af(7), "folder": f"{g}/old", "replaced_by": af(1)}
        for rows in ((p, r), (r, p)):
            with self.subTest(order=[sorted(row)[0] for row in rows]):
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
                self.fragment("20260101T000000Z-together.jsonl", *rows)
                self.assertEqual(self.snapshot(), [])
                self.assertEqual(self.resolution()["history"][("folder", f"{g}/old")], f"{g}/c")
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        one = self.fragment("20260101T000000Z-p.jsonl", p)
        two = self.fragment("20260102T000000Z-r.jsonl", r)
        self.assertEqual(self.snapshot(), [])
        self.assertIn(f"{one} and {two}, both new, touch the address {g}/old",
                      "\n".join(self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}))))

    def test_concurrent_retirements_chain_or_go_round(self) -> None:
        # From live p, q and r: one change retires p for q, another q for r. Each is valid alone; together p resolves to
        # r, in either order of the fragments, and the guard finds them independent: a replacement is read at the end.
        g = self.g
        self.remove(f"{g}/p.md")
        self.remove(f"{g}/q.md")
        self.write()
        one = {"statement": af(20), "page": f"{g}/p", "replaced_by": af(21)}
        two = {"statement": af(21), "page": f"{g}/q", "replaced_by": af(22)}
        base = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")})
        seen = []
        for names in (("20260101T000000Z-p.jsonl", "20260102T000000Z-q.jsonl"),
                      ("20260102T000000Z-p.jsonl", "20260101T000000Z-q.jsonl")):
            with self.subTest(names=names):
                shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
                self.fragment(names[0], one)
                self.fragment(names[1], two)
                self.assertEqual(self.snapshot(base=base), [])
                found = self.resolution()
                self.assertEqual(found["replacements"], {af(22): {"kind": "page", "node": f"{g}/r"}})
                self.assertEqual({key: value for key, value in found["history"].items() if key[0] == "page"},
                                 {("page", f"{g}/p"): f"{g}/r", ("page", f"{g}/q"): f"{g}/r"})
                seen.append(found)
        self.assertEqual(seen[0], seen[1])
        # p for q and q for p: a loop the combined check refuses, whatever the guard says of the pair.
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        self.fragment("20260101T000000Z-p.jsonl", one)
        self.fragment("20260102T000000Z-q.jsonl", {"statement": af(21), "page": f"{g}/q", "replaced_by": af(20)})
        errors = self.snapshot(base=base)
        self.assertIn(f"{cards.MOVES}: the replacements of {af(20)} go round", errors)

    def test_a_later_independent_fragment_on_main_forces_no_restamp(self) -> None:
        # The pull request, cut from the base, moves p in a fragment stamped first; main then gains a later fragment,
        # which moves q. On the merge commit, against the merge base and against main as it is now, the pull request
        # passes: the required step and the strict check alike.
        g = self.g
        self.branch("pr", self.base)
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.fragment("20260101T000000Z-p.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        self.commit("move p")
        self.branch("main", self.base)
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        self.fragment("20260102T000000Z-q.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        main = self.commit("move q")
        merged = self.merge("main", "pr")
        self.assertEqual(self.git("rev-parse", f"{merged}^1").strip(), main)
        for base in (self.base, main):
            with self.subTest(base=base):
                self.assertEqual(self.moves("--base", base), (0, ""))
                self.assertEqual(self.check("--base", base), (0, ""))
                self.assertEqual(self.strict(base), [])

    def test_a_dependent_misorder_fails_with_the_hint_and_passes_once_restamped(self) -> None:
        # main has m, stamped second, which moves p to f/p; a pull request made on it moves f/p on, in a fragment
        # stamped first. It builds on m and sorts before it.
        g = self.g
        self.branch("main", self.base)
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        m = self.fragment("20260102T000000Z-m.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        main = self.commit("m")
        self.branch("pr", main, self.rows)
        self.relocate(f"{g}/f/p.md", f"{g}/f/p2.md")
        p = self.fragment("20260101T000000Z-p.jsonl", {"page": f"{g}/f/p", "to": f"{g}/f/p2", "article_id": af(20)})
        self.commit("p")
        rows = self.rows
        self.merge("main", "pr")
        # The snapshot sees the order; the required step sees the crossing of m, which the base has.
        self.assertIn(f"{p}:1: it builds on {m}, which sorts after it: restamp yours with `python "
                      f"scripts/card_moves.py new-moves --restamp {p}`", "\n".join(self.snapshot()))
        crossing = (f"{p} sorts before {m}, which the base commit has, and both touch the address {g}/f/p: restamp "
                    f"it with `python scripts/card_moves.py new-moves --restamp {p}`, so that it sorts after it")
        for run in (self.moves, self.check):
            status, errors = run("--base", main)
            self.assertEqual(status, 1)
            self.assertIn(crossing, errors)
        # Restamped on its branch, the pull request's merge commit passes.
        self.branch("pr", "pr", rows)
        # The checkout is injected (wiki.ROOT): the binding to the checkout run from is NewMovesEntryPoint's.
        with contextlib.redirect_stdout(io.StringIO()), patch.object(Path, "cwd", return_value=self.tmp), \
                patch.object(card_moves, "checkout_problem", return_value=None):
            self.assertEqual(card_moves.main(["new-moves", "--restamp", p, "--base", main]), 0)
        self.commit("restamp p")
        self.git("checkout", "-q", "main")
        self.git("reset", "-q", "--hard", main)
        self.merge("main", "pr")
        self.assertEqual(self.snapshot(), [])
        self.assertEqual(self.moves("--base", main), (0, ""))
        self.assertEqual(self.check("--base", main), (0, ""))
        self.assertEqual(self.strict(main), [])

    def crossing(self, name_m: str, name_p: str) -> tuple[str, str, str]:
        """main has m (the fragment ``name_m``), which moves p to f/p; a pull request made on it moves f/p on to f/p2 in
        p (``name_p``), which sorts before m: the required step refuses the pull request's merge commit with the
        restamp hint. Checked out at the pull request's branch: main's commit and the two fragments' paths."""
        g = self.g
        self.branch("main", self.base)
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        m = self.fragment(name_m, {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        main = self.commit("m")
        self.branch("pr", main, self.rows)
        self.relocate(f"{g}/f/p.md", f"{g}/f/p2.md")
        p = self.fragment(name_p, {"page": f"{g}/f/p", "to": f"{g}/f/p2", "article_id": af(20)})
        self.commit("p")
        rows = self.rows
        self.merge("main", "pr")
        status, errors = self.moves("--base", main)
        self.assertEqual(status, 1)
        self.assertIn(f"{p} sorts before {m}, which the base commit has, and both touch the address {g}/f/p: restamp "
                      f"it with `python scripts/card_moves.py new-moves --restamp {p}`, so that it sorts after it",
                      errors)
        self.branch("pr", "pr", rows)
        return main, p, m

    def passes_merged(self, main: str) -> None:
        """The pull request, its fragment restamped, merged again into main: the snapshot, the required step and the
        card check's ledger check pass."""
        self.commit("restamp p")
        self.git("checkout", "-q", "main")
        self.git("reset", "-q", "--hard", main)
        self.merge("main", "pr")
        self.assertEqual(self.snapshot(), [])
        self.assertEqual(self.moves("--base", main), (0, ""))
        self.assertEqual(self.strict(main), [])

    def entry_point(self) -> None:
        """scripts/card_moves.py, copied beside the checkout's ledger, so that the required check and new-moves run as
        themselves; kept out of the checkout's commits."""
        scripts = self.tmp / "scripts"
        if not (scripts / "card_moves.py").exists():
            for module in NewMovesEntryPoint.MODULES:
                shutil.copyfile(Path(cards.__file__).resolve().parent / module, scripts / module)
            exclude = self.tmp / ".git" / "info" / "exclude"
            exclude.parent.mkdir(exist_ok=True)
            with exclude.open("a") as handle:
                handle.write("/scripts/*.py\n")

    def new_moves(self, *arguments: str) -> tuple[int, str, str]:
        """`python scripts/card_moves.py new-moves …` run as itself from the checkout (entry_point), with no root
        injected, on the real clock."""
        self.entry_point()
        result = subprocess.run([sys.executable, "scripts/card_moves.py", "new-moves", *arguments], cwd=self.tmp,
                                capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        return result.returncode, result.stdout, result.stderr

    def test_the_required_check_gives_the_moves_check_s_errors_that_need_no_tree(self) -> None:
        # One fragment breaking a rule among the rows (an address moved twice) and rules against the tree (a page that
        # moved and is still there, chains ending elsewhere than their articles): the moves check gives them all, the
        # required check only the first; with nothing wrong among the rows, it passes what the moves check refuses.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        path = self.fragment("20260101T000000Z-p.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)},
                             {"page": f"{g}/p", "to": f"{g}/f/p3", "article_id": af(20)},
                             {"page": f"{g}/q", "to": f"{g}/nowhere", "article_id": af(21)})
        self.commit("p")
        status, errors = self.moves("--base", self.base)
        self.assertEqual(status, 1)
        for error in (f"{path}:2: {g}/p already moved", f"card-moves.jsonl: the page {g}/q moved but is still there",
                      f"card-moves.jsonl: {g}/q ends at {g}/nowhere, but {af(21)} is {g}/q"):
            self.assertIn(error, errors)
        self.assertEqual(self.check("--base", self.base), (1, f"error: {path}:2: {g}/p already moved\n"))
        (self.tmp / path).write_text(json.dumps({"page": f"{g}/q", "to": f"{g}/nowhere", "article_id": af(21)}) + "\n")
        self.assertEqual(self.moves("--base", self.base)[0], 1)
        self.assertEqual(self.check("--base", self.base), (0, ""))
        # A usage error is one, and a missing frozen file is said as the moves check says it.
        self.assertEqual(self.check("--base")[0], 1)
        self.assertEqual(self.check("extra")[0], 2)
        (self.tmp / cards.FROZEN).unlink()
        self.assertEqual(self.check(), (1, "error: card-moves.jsonl: missing; the moves check certifies a ledger that "
                                           "exists\n"))
        self.assertEqual(self.moves()[0], 1)

    def test_the_required_check_holds_each_history_to_its_rows(self) -> None:
        # What the rows alone say about one article, the required check holds: a retired article's moves end at the
        # address its retirement records, as the kind it is retired as; an article retired as neither ends at one
        # address; a retired card's replacements end at no retired statement and no page; what ends at a retired address
        # is its final replacement; and an address has one owner, page and folder alike: two articles end at no one
        # address, and none at one another article moved away from. Each case is refused by the required check, run as
        # itself, and by the moves check alike (moves, which holds the two to the same errors but the tree's); each
        # consistent variant passes the required check, whatever the tree then says of where its articles live.
        g = self.g
        x, y, folder, other, card = af(20), af(22), af(50), af(21), af(1)

        def page(old: str, new: str, article: str) -> dict:
            return {"page": f"{g}/{old}", "to": f"{g}/{new}", "article_id": article}

        def moved_folder(old: str, new: str, article: str) -> dict:
            return {"folder": f"{g}/{old}", "to": f"{g}/{new}", "article_id": article}

        def statement(article: str, address: str, successor: str) -> dict:
            return {"statement": article, "page": f"{g}/{address}", "replaced_by": successor}

        def retired_card(article: str, address: str, successor: str) -> dict:
            return {"card": article, "folder": f"{g}/{address}", "replaced_by": successor}

        cases = [
            ("a statement retired where its page is not", [page("p", "second", x), statement(x, "unrelated", y)],
             f"the page {g}/p ends at {g}/second, but its statement {x} was retired at {g}/unrelated"),
            ("a statement retired where its page is", [page("p", "second", x), statement(x, "second", y)], None),
            ("a card retired where its folder is not", [moved_folder("f", "f2", folder),
                                                        retired_card(folder, "elsewhere", card)],
             f"the folder {g}/f ends at {g}/f2, but its card {folder} was retired at {g}/elsewhere"),
            ("a card retired where its folder is", [moved_folder("f", "f2", folder), retired_card(folder, "f2", card)],
             None),
            ("a page retired as a card", [page("p", "p2", x), retired_card(x, "p2", card)],
             f"the page {g}/p ends at {g}/p2, but {x} was retired as a card, which is a folder"),
            ("a folder retired as a statement", [moved_folder("f", "f2", folder), statement(folder, "f2", y)],
             f"the folder {g}/f ends at {g}/f2, but {folder} was retired as a statement, which is a page"),
            ("two chains of one article ending apart", [page("p", "p2", x), page("old", "p3", x)],
             f"the moves of {x} end at 2 addresses, {g}/p2 as a page, {g}/p3 as a page; an article lives at one "
             "address, as a page or as a folder"),
            ("a page and a folder of one article", [page("p", "p2", x), moved_folder("old", "new", x)],
             f"the moves of {x} end at 2 addresses, {g}/new as a folder, {g}/p2 as a page; an article lives at one "
             "address, as a page or as a folder"),
            ("two chains of one article ending together", [page("p", "p2", x), page("p2", "p3", x)], None),
            ("a card replaced by a retired statement", [statement(y, "r", x), retired_card(card, "c", y)],
             f"the retired card {card} is replaced by {y}, a retired statement, which is no card"),
            ("a card replaced by a page", [page("q", "q2", other), retired_card(card, "c", other)],
             f"the retired card {card} is replaced by {other}, which moved as a page, so is no card"),
            ("a card replaced by a folder", [moved_folder("f", "f2", folder), retired_card(card, "c", folder)], None),
            ("another article at a retired statement's address", [statement(x, "p", y), page("q", "p", other)],
             f"{g}/p is the last address of the retired statement {x}, replaced by {y}, and the page {g}/q ends there "
             f"as {other}; an address has one owner"),
            ("the final replacement at a retired statement's address", [statement(x, "p", y), page("r", "p", y)],
             None),
            ("another article at a retired card's address", [retired_card(card, "c", af(60)),
                                                             moved_folder("f", "c", folder)],
             f"{g}/c is the last address of the retired card {card}, replaced by {af(60)}, and the folder {g}/f ends "
             f"there as {folder}; an address has one owner"),
            ("the final replacement at a retired card's address", [retired_card(card, "c", folder),
                                                                   moved_folder("f", "c", folder)], None),
            ("two articles ending at one address", [page("p", "b", x), page("q", "b", other)],
             f"the moves of 2 articles end at {g}/b, {x} from the page {g}/p, {other} from the page {g}/q; an address "
             "has one owner"),
            ("a page and a folder ending at one address", [page("p", "b", x), moved_folder("f", "b", folder)],
             f"the moves of 2 articles end at {g}/b, {x} from the page {g}/p, {folder} from the folder {g}/f; an "
             "address has one owner"),
            ("two articles ending apart", [page("p", "b", x), page("q", "c", other)], None),
            ("a folder at the address a page left", [page("p", "p2", x), moved_folder("f", "p", folder)],
             f"{x} moved from {g}/p as a page, and the folder {g}/f ends there as {folder}; an address has one owner"),
            ("a page at the address a folder left", [moved_folder("f", "f2", folder), page("p", "f", x)],
             f"{folder} moved from {g}/f as a folder, and the page {g}/p ends there as {x}; an address has one owner"),
            ("a folder at the address a statement was retired at, for it", [statement(x, "p", folder),
                                                                           moved_folder("f", "p", folder)], None),
            ("three owners of one address, each retired for the next", [
                statement(x, "s", other), page("q", "s", other), statement(other, "s", y), page("r", "s", y)], None),
        ]
        path = f"{cards.FRAGMENTS}/20260101T000000Z-rows.jsonl"
        for name, rows, error in cases:
            with self.subTest(case=name):
                self.fragment("20260101T000000Z-rows.jsonl", *rows)
                status, said = self.check()
                if error is None:
                    self.assertEqual((status, said), (0, ""))
                else:
                    self.assertEqual(status, 1)
                    self.assertIn(f"error: card-moves.jsonl: {error}\n", said)
                    self.assertEqual(self.moves()[0], 1)
                self.moves()
                self.moves("--base", self.base)
                (self.tmp / path).unlink()

    def test_two_owners_of_one_address_are_refused_however_the_rows_are_split(self) -> None:
        # The two forms of two owners of one address, two articles ending there and one ending where another moved away
        # from as the other kind, each split as a published fragment and a new one that sorts after it, so that the
        # guard, which holds a new fragment only to the published ones sorting after it, finds nothing: the required
        # check refuses the combined ledger against that base, and without a base, as the moves check does.
        g = self.g
        x, other, folder = af(20), af(21), af(50)
        forms = [
            ("two articles ending at one address", {"page": f"{g}/p", "to": f"{g}/b", "article_id": x},
             {"folder": f"{g}/f", "to": f"{g}/b", "article_id": folder},
             f"the moves of 2 articles end at {g}/b, {x} from the page {g}/p, {folder} from the folder {g}/f; an "
             "address has one owner"),
            ("a page at the address a folder left", {"folder": f"{g}/f", "to": f"{g}/f2", "article_id": folder},
             {"page": f"{g}/q", "to": f"{g}/f", "article_id": other},
             f"{folder} moved from {g}/f as a folder, and the page {g}/q ends there as {other}; an address has one "
             "owner"),
        ]
        for name, published_row, new_row, error in forms:
            with self.subTest(form=name):
                self.branch(name.replace(" ", "-"), self.base)
                self.fragment("20260101T000000Z-published.jsonl", published_row)
                published = self.commit("published")
                self.fragment("20260102T000000Z-new.jsonl", new_row)
                self.commit("new")
                for arguments in (("--base", published), ()):
                    status, said = self.check(*arguments)
                    self.assertEqual(status, 1)
                    self.assertIn(f"error: card-moves.jsonl: {error}\n", said)
                    self.assertNotIn("both new", said)
                    self.assertNotIn("sorts before", said)
                    self.assertEqual(self.moves(*arguments)[0], 1)
                self.git("checkout", "-q", "main")

    def test_the_live_folders_are_regular_folder_pages_in_both_checks(self) -> None:
        # A folder whose folder page is a link, to a file or to nothing, or a submodule, is no live folder, in the
        # commit's tree entries (card_moves.live_folders, the required check's) and in the checked-out tree
        # (cards.LiveFolders, the moves check's) alike: two new fragments leaving it interact through it, and both
        # checks refuse them; under a folder with a regular folder page, they pass.
        g = self.g
        layout = {"linked": ("../f/README.md", 31), "dangling": ("not-a-page.md", 33), "submodule": (None, 35),
                  "regular": ("", 37)}
        for name, (target, number) in layout.items():
            folder = wiki.ROADMAP / g / name
            folder.mkdir(parents=True)
            for offset in (0, 1):
                self.leaf(f"{g}/{name}/p{offset}.md", number + offset, facts=None)
            if target == "":
                (folder / "README.md").write_text(f"# {name}\n")
            elif target is not None:
                (folder / "README.md").symlink_to(target)
            else:
                inner = folder / "README.md"
                inner.mkdir()
                for arguments in (("init", "-q"), ("commit", "-q", "--allow-empty", "-m", "inner")):
                    subprocess.run(["git", *arguments], cwd=inner, check=True, capture_output=True,
                                   env={**os.environ, "GIT_AUTHOR_NAME": "A", "GIT_AUTHOR_EMAIL": "a@example.org",
                                        "GIT_COMMITTER_NAME": "A", "GIT_COMMITTER_EMAIL": "a@example.org"})
        structure = self.commit("structure")
        at_structure = copy.deepcopy(self.rows)
        modes = {line.split("\t", 1)[1].rsplit("/", 2)[-2]: line.split()[0]
                 for line in self.git("ls-tree", "-r", "HEAD", "--", f"blueprint/roadmap/{g}").splitlines()
                 if line.endswith("/README.md")}
        self.assertEqual({name: modes[name] for name in layout}, {"linked": "120000", "dangling": "120000",
                                                                  "submodule": "160000", "regular": "100644"})
        live = card_moves.live_folders(self.tmp)
        for name in layout:
            self.assertEqual((name, f"{g}/{name}" in live, f"{g}/{name}" in cards.LiveFolders()),
                             (name, name == "regular", name == "regular"))
        self.assertEqual(live, frozenset(folder for folder in live | {f"{g}/{name}" for name in layout}
                                         if folder in cards.LiveFolders()))
        for name, (_, number) in layout.items():
            with self.subTest(folder=name):
                for offset in (0, 1):
                    self.relocate(f"{g}/{name}/p{offset}.md", f"{g}/{name}-p{offset}.md")
                    self.fragment(f"2026010{offset + 1}T000000Z-{name}.jsonl",
                                  {"page": f"{g}/{name}/p{offset}", "to": f"{g}/{name}-p{offset}",
                                   "article_id": af(number + offset)})
                self.commit(f"moves out of {name}")
                status, errors = self.moves("--base", structure)
                both = f"both new, touch the address {g}/{name}:"
                self.assertEqual((status, both in errors), (0, False) if name == "regular" else (1, True), errors)
                self.assertEqual(self.check("--base", structure)[0], status)
                self.git("reset", "-q", "--hard", structure)
                self.rows = copy.deepcopy(at_structure)

    def test_the_required_check_reads_the_roadmap_s_folders_by_name_from_the_commit(self) -> None:
        # The guard's live folders, which the required check reads from the commit checked out: the folders with a
        # folder page, a regular file, by the names, modes and types of Git's tree entries, as the moves check finds
        # them in the checked-out tree.
        def checked_out() -> frozenset[str]:
            return frozenset(page.parent.relative_to(wiki.ROADMAP).as_posix()
                             for page in wiki.ROADMAP.rglob("README.md") if page.parent != wiki.ROADMAP)

        tree = checked_out()
        self.assertTrue({"Algebra", "Algebra/groups", "Algebra/groups/c", "Algebra/groups/f"} <= tree, tree)
        self.assertEqual(card_moves.live_folders(self.tmp), tree)
        self.assertEqual(frozenset(folder for folder in tree if folder in cards.LiveFolders()), tree)
        # A folder page made or removed since is not the commit's, until it is committed.
        (wiki.ROADMAP / "Algebra/groups/f/README.md").unlink()
        self.folder("Algebra/groups/n/README.md", "N", [])
        self.assertEqual(card_moves.live_folders(self.tmp), tree)
        self.commit("n")
        self.assertEqual(card_moves.live_folders(self.tmp), checked_out())
        self.assertEqual(checked_out(), tree - {"Algebra/groups/f"} | {"Algebra/groups/n"})
        # A commit Git cannot read is an error, never an empty set.
        with self.assertRaises(subprocess.CalledProcessError):
            card_moves.live_folders(self.tmp, "f" * 40)

    def test_the_required_check_reads_no_file_outside_the_ledger(self) -> None:
        # The required check reads the ledger's files, the base's ledger from Git's trees and, of the rest of the tree,
        # only names: with every other file gone from the checkout and every other blob gone from Git, it says what it
        # said with them. A pull request's merge commit whose fragment and main's meet only above a live folder, which
        # the guard reads the names for, passes; with a new fragment that crosses main's, it is refused.
        g = self.g
        self.branch("pr", self.base)
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.fragment("20260101T000000Z-p.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        self.commit("move p")
        self.branch("main", self.base)
        self.relocate(f"{g}/q.md", f"{g}/f/q.md")
        q = self.fragment("20260102T000000Z-q.jsonl", {"page": f"{g}/q", "to": f"{g}/f/q", "article_id": af(21)})
        main = self.commit("move q")
        self.merge("main", "pr")
        crossing = f"{cards.FRAGMENTS}/20260101T000001Z-x.jsonl"

        def runs() -> list[tuple[int, str]]:
            said = []
            for row in (None, {"page": f"{g}/f/q", "to": f"{g}/f/q2", "article_id": af(21)}):
                if row is not None:
                    (self.tmp / crossing).write_text(json.dumps(row) + "\n")
                said += [self.check("--base", main), self.check()]
                (self.tmp / crossing).unlink(missing_ok=True)
            return said

        said = runs()
        self.assertEqual([status for status, _ in said], [0, 0, 1, 1])
        self.assertIn(f"{crossing} sorts before {q}, which the base commit has, and both touch the address {g}/f/q",
                      said[2][1])
        # Every blob of the two commits but the ledger's, gone from Git (a repository this small keeps each object in a
        # file of its own), and every file of the checkout but the ledger's and the script, gone from it.
        gone = set()
        for commit in (main, "HEAD"):
            for line in self.git("ls-tree", "-r", commit).splitlines():
                head, path = line.split("\t", 1)
                if not path.startswith((cards.FROZEN, f"{cards.FRAGMENTS}/")):
                    gone.add(head.split()[2])
        readme = self.git("rev-parse", f"HEAD:blueprint/roadmap/{g}/README.md").strip()
        self.assertIn(readme, gone)
        for oid in gone:
            (self.tmp / ".git" / "objects" / oid[:2] / oid[2:]).unlink()
        self.assertNotEqual(subprocess.run(["git", "-C", str(self.tmp), "cat-file", "-e", readme]).returncode, 0)
        shutil.rmtree(self.tmp / "blueprint")
        self.assertEqual(runs(), said)

    def test_a_restamp_passes_a_published_fragment_stamped_ahead(self) -> None:
        # m, on main, is stamped half an hour ahead of the clock, as the required step lets a new fragment be. A restamp
        # to the current time would still sort p before it; the restamp names p one second after m.
        ahead = datetime.now(timezone.utc).replace(microsecond=0) + timedelta(minutes=30)
        main, p, m = self.crossing(f"{ahead:%Y%m%dT%H%M%SZ}-m.jsonl", "20260101T000000Z-p.jsonl")
        renamed = f"{cards.FRAGMENTS}/{ahead + timedelta(seconds=1):%Y%m%dT%H%M%SZ}-p.jsonl"
        self.assertEqual(self.new_moves("--restamp", p, "--base", main), (0, f"{p} -> {renamed}\n", ""))
        self.assertTrue((self.tmp / renamed).is_file())
        self.passes_merged(main)

    def test_a_restamp_passes_a_published_fragment_of_the_same_second_with_a_later_slug(self) -> None:
        # q, on main, is stamped in the very second of the clock; p, of that second too, sorts before it by its slug. A
        # restamp to the current time would keep p's name; the restamp names p one second after q. (The clock is set
        # to that second, in this process.)
        second = datetime(2026, 1, 2, tzinfo=timezone.utc)
        main, p, m = self.crossing("20260102T000000Z-q.jsonl", "20260102T000000Z-p.jsonl")
        out = io.StringIO()
        with contextlib.redirect_stdout(out), patch.object(Path, "cwd", return_value=self.tmp), \
                patch.object(card_moves, "checkout_problem", return_value=None), \
                patch.object(card_moves, "utc_now", return_value=second):
            self.assertEqual(card_moves.main(["new-moves", "--restamp", p, "--base", main]), 0)
        self.assertEqual(out.getvalue(), f"{p} -> {cards.FRAGMENTS}/20260102T000001Z-p.jsonl\n")
        self.passes_merged(main)

    def test_no_helper_names_a_fragment_more_than_an_hour_ahead(self) -> None:
        # m, on main, is stamped an hour and five minutes ahead of the clock: a fragment sorting after it would be
        # stamped ahead by more than the required step allows. The restamp, and new-moves, refuse, writing nothing,
        # and say when they can run.
        far = datetime.now(timezone.utc).replace(microsecond=0) + timedelta(hours=1, minutes=5)
        main, p, m = self.crossing(f"{far:%Y%m%dT%H%M%SZ}-m.jsonl", "20260101T000000Z-p.jsonl")
        when = f"run again at {far + timedelta(seconds=1) - timedelta(hours=1):%Y-%m-%d %H:%M:%S} UTC or later"
        self.entry_point()
        for arguments in (("--restamp", p, "--base", main), ("next-change", "--base", main),
                          ("next-change", "--take-appended", "--base", main)):
            with self.subTest(arguments=arguments):
                if "--take-appended" in arguments:
                    frozen = wiki.ROOT / "scripts" / cards.MOVES
                    frozen.write_text(frozen.read_text() + json.dumps(
                        {"page": f"{self.g}/r", "to": f"{self.g}/r2", "article_id": af(22)}) + "\n")
                before = entries(self.tmp)
                status, out, errors = self.new_moves(*arguments)
                self.assertEqual((status, out), (1, ""))
                self.assertTrue(errors.startswith(f"error: {m} is stamped {far:%Y-%m-%d %H:%M:%S} UTC: a fragment "
                                                  "sorting after it would be stamped more than an hour ahead of the "
                                                  "clock, "), errors)
                self.assertTrue(errors.endswith(f"; {when}\n"), errors)
                self.assertEqual(entries(self.tmp), before)

    def test_no_helper_names_a_fragment_after_the_last_stamp_a_name_can_have(self) -> None:
        # A fragment stamped 9999-12-31 23:59:59, the last stamp a fragment's name can have (its year has four digits),
        # in the checkout and, separately, in the base: no fragment can sort after it, now or later. Each mode refuses
        # through the real entry point, naming it and saying that waiting will not help, and the checkout is unchanged,
        # entry by entry; one stamped a second earlier still gets the refusal that says when to run again.
        g = self.g
        last = f"{cards.FRAGMENTS}/99991231T235959Z-zz.jsonl"
        row = json.dumps({"page": f"{g}/older", "to": f"{g}/p", "article_id": af(20)}) + "\n"
        added = json.dumps({"page": f"{g}/r", "to": f"{g}/r2", "article_id": af(22)}) + "\n"
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        published = frozen.read_text()
        self.entry_point()
        tail = ("holds the last stamp a fragment's name can have, 9999-12-31 23:59:59 UTC: no later four-digit stamp "
                "exists, so no fragment can sort after it, and waiting will not help; rename or remove that fragment\n")

        def refused(base: str, where: str) -> None:
            # p, a fragment the base lacks, for --restamp; a row beyond the base's frozen file, for --take-appended.
            p = self.fragment("20260101T000000Z-p.jsonl", text=row)
            frozen.write_text(published + added)
            for mode, arguments in (("new-moves", ("next-change", "--base", base)),
                                    ("--take-appended", ("next-change", "--take-appended", "--base", base)),
                                    ("--restamp", ("--restamp", p, "--base", base))):
                with self.subTest(where=where, mode=mode):
                    before = entries(self.tmp)
                    self.assertEqual(self.new_moves(*arguments), (1, "", f"error: {where} {tail}"))
                    self.assertEqual(entries(self.tmp), before)
            (self.tmp / p).unlink()
            frozen.write_text(published)

        # In the checkout only.
        (self.tmp / last).parent.mkdir(exist_ok=True)
        (self.tmp / last).write_text(row)
        refused(self.base, last)
        # In the base only: committed, then gone from the checkout.
        holding = self.commit("the last stamp")
        (self.tmp / last).unlink()
        refused(holding, f"{last} at {holding}")
        # A second earlier, a stamp after it exists: the refusal says when to run again.
        earlier = f"{cards.FRAGMENTS}/99991231T235958Z-zy.jsonl"
        (self.tmp / earlier).write_text(row)
        before = entries(self.tmp)
        status, out, errors = self.new_moves("next-change", "--base", self.base)
        self.assertEqual((status, out), (1, ""))
        self.assertTrue(errors.startswith(f"error: {earlier} is stamped 9999-12-31 23:59:58 UTC: a fragment sorting "
                                          "after it would be stamped more than an hour ahead of the clock, "), errors)
        self.assertTrue(errors.endswith("; run again at 9999-12-31 22:59:59 UTC or later\n"), errors)
        self.assertEqual(entries(self.tmp), before)

    def test_no_helper_reads_a_base_it_cannot_read_in_full(self) -> None:
        # A base whose ledger cannot be read in full is refused, as the check refuses it, never taken for a shorter
        # one: its folder of fragments holding a misnamed file, or an empty fragment; or fragments and no frozen file.
        # Each mode refuses through the real entry point, naming the base and the problem, and the checkout is
        # unchanged, entry by entry.
        g = self.g
        row = json.dumps({"page": f"{g}/older", "to": f"{g}/p", "article_id": af(20)}) + "\n"
        added = json.dumps({"page": f"{g}/r", "to": f"{g}/r2", "article_id": af(22)}) + "\n"
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        published = frozen.read_text()
        self.entry_point()

        def base_with(label: str, entries: dict[str, str], keep_frozen: bool = True) -> str:
            """A commit on main whose folder of fragments holds ``entries`` (by name), with or without the frozen
            file; then the checkout put back as it was, at the base commit."""
            self.branch(label, self.base)
            folder = wiki.ROOT / cards.FRAGMENTS
            folder.mkdir(exist_ok=True)
            for name, text in entries.items():
                (folder / name).write_text(text)
            if not keep_frozen:
                frozen.unlink()
            commit = self.commit(label)
            self.git("checkout", "-q", "main")
            self.git("reset", "-q", "--hard", self.base)
            self.git("clean", "-q", "-f", "-d", "--", "scripts")
            self.rows = copy.deepcopy(self.at_base)
            return commit

        cases = [
            ("a misnamed file", base_with("misnamed", {"20260101T000000Z-a.jsonl": row, "notes.txt": row}),
             "scripts/card-moves.d/notes.txt: not a fragment; a fragment is a file named "
             "<YYYYMMDDTHHMMSSZ>-<slug>.jsonl"),
            ("an empty fragment", base_with("empty", {"20260101T000000Z-a.jsonl": row,
                                                      "20260102T000000Z-empty.jsonl": ""}),
             "scripts/card-moves.d/20260102T000000Z-empty.jsonl: no row; a fragment holds at least one"),
            ("no frozen file", base_with("unfrozen", {"20260101T000000Z-a.jsonl": row}, keep_frozen=False),
             "there is no scripts/card-moves.jsonl"),
        ]
        for label, base, problem in cases:
            # p, a fragment of the checkout the base lacks, for --restamp; a row beyond the frozen file, for
            # --take-appended.
            p = self.fragment("20260103T000000Z-p.jsonl", text=row)
            frozen.write_text(published + added)
            for mode, arguments in (("new-moves", ("next-change", "--base", base)),
                                    ("--take-appended", ("next-change", "--take-appended", "--base", base)),
                                    ("--restamp", ("--restamp", p, "--base", base))):
                with self.subTest(case=label, mode=mode):
                    before = entries(self.tmp)
                    status, out, errors = self.new_moves(*arguments)
                    self.assertEqual((status, out), (1, ""))
                    self.assertTrue(errors.startswith(f"error: --base {base}: the commit's move ledger cannot be read "
                                                      "in full ("), errors)
                    self.assertIn(problem, errors)
                    self.assertTrue(errors.endswith("): a new name sorts after every fragment of the checkout and of "
                                                    "that commit, so it must be read\n"), errors)
                    self.assertEqual(entries(self.tmp), before)
            (self.tmp / p).unlink()
            frozen.write_text(published)
        # The control: the base itself, whose ledger reads in full, lets each mode write.
        p = self.fragment("20260103T000000Z-p.jsonl", text=row)
        self.assertEqual(self.new_moves("--restamp", p, "--base", self.base)[0], 0)
        self.assertEqual(self.new_moves("next-change", "--base", self.base)[0], 0)

    def test_a_new_fragment_sorts_after_a_published_fragment_stamped_ahead(self) -> None:
        # m, on main, is stamped half an hour ahead of the clock: new-moves names a new fragment one second after it,
        # so that it does not start out sorting before m; without a base it can read, it names none and writes
        # nothing, the folder of fragments included.
        ahead = datetime.now(timezone.utc).replace(microsecond=0) + timedelta(minutes=30)
        self.branch("main", self.base)
        m = self.fragment(f"{ahead:%Y%m%dT%H%M%SZ}-m.jsonl", text=json.dumps(
            {"page": f"{self.g}/older", "to": f"{self.g}/p", "article_id": af(20)}) + "\n")
        self.commit("m")
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        made = f"{cards.FRAGMENTS}/{ahead + timedelta(seconds=1):%Y%m%dT%H%M%SZ}-next-change.jsonl"
        self.entry_point()
        before = entries(self.tmp)
        status, out, errors = self.new_moves("next-change", "--base", "nowhere")
        self.assertEqual((status, out), (1, ""))
        self.assertIn("error: --base nowhere is no commit Git can read here", errors)
        self.assertEqual(entries(self.tmp), before)
        status, out, errors = self.new_moves("next-change", "--base", "main")
        self.assertEqual((status, errors), (0, ""))
        self.assertTrue(out.startswith(f"{made}: add the change's rows to it"), out)
        self.assertEqual((self.tmp / made).read_bytes(), b"")
        self.assertFalse((self.tmp / m).exists())

    def test_independent_fragments_give_one_resolution_in_either_order(self) -> None:
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        self.remove(f"{g}/q.md")
        self.write()
        move = {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)}
        retire = {"statement": af(21), "page": f"{g}/q", "replaced_by": af(22)}
        found = []
        for names in (("20260101T000000Z-a.jsonl", "20260102T000000Z-b.jsonl"),
                      ("20260102T000000Z-a.jsonl", "20260101T000000Z-b.jsonl")):
            shutil.rmtree(wiki.ROOT / cards.FRAGMENTS, ignore_errors=True)
            self.fragment(names[0], move)
            self.fragment(names[1], retire)
            self.assertEqual(self.snapshot(base=card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")})), [])
            # Both are new against the base commit, which has the frozen file alone: the required check passes them.
            self.assertEqual(self.check("--base", self.base), (0, ""))
            found.append(self.resolution())
        self.assertEqual(found[0], found[1])
        self.assertEqual(found[0]["history"], {("page", f"{g}/p"): f"{g}/f/p", ("page", f"{g}/q"): f"{g}/r"})

    def test_a_stacked_fragment_is_published_once_its_change_lands(self) -> None:
        # The first change of a stack lands with f1; the second, made on it, adds f2: against the new base, f1 is
        # published, unchanged, and only f2 is new.
        g = self.g
        self.relocate(f"{g}/p.md", f"{g}/f/p.md")
        f1 = self.fragment("20260101T000000Z-first.jsonl", {"page": f"{g}/p", "to": f"{g}/f/p", "article_id": af(20)})
        landed = self.commit("first")
        self.relocate(f"{g}/f/p.md", f"{g}/f/p2.md")
        self.fragment("20260102T000000Z-second.jsonl", {"page": f"{g}/f/p", "to": f"{g}/f/p2", "article_id": af(20)})
        self.commit("second")
        self.assertEqual(self.moves("--base", landed), (0, ""))
        self.assertEqual(self.strict(landed), [])
        (self.tmp / f1).write_text("")
        status, errors = self.moves("--base", landed)
        self.assertEqual(status, 1)
        self.assertIn(f"{f1}: no row", errors)
        self.assertIn(f"{f1}, a fragment of the base commit, is gone", errors)


class RequiredCheckClosure(unittest.TestCase):
    """The required check's code is scripts/card_moves.py alone: it imports the standard library only, and its text
    names no file of the repository but the ledger's and its own, read as a scanner of the code behind a required check
    reads a script (main's merge-queue preflight): any path from the repository's root, any file at the root named
    alone, any glob over the repository's paths, any script named alone beside it, and any module imported from beside
    it. The ledger's files are named so that such a scanner watches every fragment, before the first and after it: the
    frozen file by its path, and the fragments by the glob of their files. Its one read beyond the ledger, the tree
    entries below the roadmap, is a folder, which such a scanner neither follows nor counts."""

    def test_the_required_check_imports_the_standard_library_alone(self) -> None:
        tree = ast.parse(Path(card_moves.__file__).read_text())
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {alias.name.split(".")[0] for alias in node.names}
            elif isinstance(node, ast.ImportFrom):
                self.assertEqual(node.level, 0, ast.dump(node))
                imported.add(node.module.split(".")[0])
        self.assertEqual(sorted(name for name in imported if name not in sys.stdlib_module_names | {"__future__"}), [])

    @staticmethod
    def named(text: str, root: Path, here: str) -> set[str]:
        """The repository files the script at ``here`` (a folder, from ``root``) names in ``text``: a path from the
        root that is a file there, or that reads as one it may come to hold (a name with an extension, below a folder
        that is no host's, with no `..`); a file at the root, named alone; a script beside it, named alone; and a
        module it imports from beside it."""
        text = re.sub(r"\$\{?\w+\}?/", "", text).replace('"', " ").replace("'", " ")
        found = set()
        for ref in (re.sub(r"^(?:\./)+", "", ref) for ref in
                    re.findall(r"(?<![\w/-])((?:\./)*[\w.-]+(?:/[\w.*-]+)+)", text)):
            parts = ref.split("/")
            if "*" in ref:
                if ".." not in parts and "." not in parts[0].lstrip("."):
                    found.add(f"glob:{ref}")
            elif (root / ref).is_file() or (not (root / ref).is_dir() and re.search(r"\.\w+$", ref)
                                            and "." not in parts[0].lstrip(".") and ".." not in parts):
                found.add(ref)
        found |= {name for name in re.findall(r"(?<![\w/.-])([\w-]+\.\w+)(?![\w/])", text) if (root / name).is_file()}
        found |= {f"{here}/{name}" for name in re.findall(r"(?<![\w/.-])([\w-]+\.(?:sh|py|bash))\b", text)
                  if (root / here / name).is_file()}
        found |= {f"{here}/{module}.py" for module in re.findall(r"^\s*(?:from|import)\s+([A-Za-z_]\w*)", text, re.M)
                  if (root / here / f"{module}.py").is_file()}
        return found

    def test_the_required_check_names_no_file_but_the_ledger_s(self) -> None:
        root = Path(card_moves.__file__).resolve().parents[1]
        text = Path(card_moves.__file__).read_text()
        # Exactly itself, the frozen file and the glob of the fragments' files, whether or not the folder exists yet;
        # the folder's own path counts only while it does not, as a file the checks may come to read.
        ledger = {"scripts/card_moves.py", card_moves.FROZEN, f"glob:{card_moves.FRAGMENT_FILES}"}
        for folder in (False, True):
            with self.subTest(folder=folder), tempfile.TemporaryDirectory() as checkout:
                (Path(checkout) / "scripts").mkdir()
                shutil.copyfile(Path(card_moves.__file__), Path(checkout) / "scripts" / "card_moves.py")
                (Path(checkout) / card_moves.FROZEN).write_text("")
                if folder:
                    (Path(checkout) / card_moves.FRAGMENTS).mkdir()
                    (Path(checkout) / card_moves.FRAGMENTS / "20260101T000000Z-a.jsonl").write_text("{}\n")
                self.assertEqual(self.named(text, Path(checkout), "scripts"),
                                 ledger | ({card_moves.FRAGMENTS} if not folder else set()))
        found = self.named(text, root, "scripts")
        self.assertLessEqual(found, ledger | {card_moves.FRAGMENTS}, found - ledger)
        # The glob is the reader's own: every fragment is one of its files, and an entry that is not, none.
        self.assertIsNone(card_moves.name_problem("20260101T000000Z-a.jsonl"))
        self.assertIsNotNone(card_moves.name_problem("20260101T000000Z-a.json"))
        # The scanner is no straw man: it finds the scripts behind the moves check, and their reads.
        cards_found = self.named(Path(cards.__file__).read_text(), root, "scripts")
        self.assertTrue({"scripts/card_moves.py", "scripts/generate_wiki.py", "scripts/sync_wiki.py"} <= cards_found,
                        cards_found)
        # The folder it lists, a folder's path with no extension, the scanner counts as no file.
        self.assertNotIn(card_moves.ROADMAP, found)


class NewMoves(Vault):
    """`scripts/card_moves.py new-moves` starts a fragment named with the current UTC time; with --take-appended it
    moves the rows a branch appended to the frozen file into it, and with --restamp it renames a fragment the base does
    not have to the current time (docs/cards.md#move-ledger). None of them writes over a file."""

    git = LedgerCheck.git
    NOW = datetime(2026, 11, 24, 12, 30, 5, tzinfo=timezone.utc)

    def setUp(self) -> None:
        super().setUp()
        self.g = g = "Algebra/groups"
        self.published = json.dumps({"page": f"{g}/old", "to": f"{g}/p", "article_id": af(20)}) + "\n"
        self.added = [{"page": f"{g}/older", "to": f"{g}/q", "article_id": af(21)},
                      {"page": f"{g}/oldest", "to": f"{g}/r", "article_id": af(22)}]
        for name, number in (("p", 20), ("q", 21), ("r", 22)):
            self.leaf(f"{g}/{name}.md", number, facts=None)
        self.write()
        (wiki.ROOT / "scripts" / cards.MOVES).write_text(self.published)
        self.git("init", "-q", "-b", "main")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")
        self.clock = patch.object(card_moves, "utc_now", return_value=self.NOW)
        self.clock.start()
        self.addCleanup(self.clock.stop)
        # The checkout is injected here (wiki.ROOT); the binding of the helpers to the checkout they are run from is
        # NewMovesEntryPoint's, through the script itself.
        bound = patch.object(card_moves, "checkout_problem", return_value=None)
        bound.start()
        self.addCleanup(bound.stop)

    def run_new_moves(self, *arguments: str) -> tuple[int, str, str]:
        out, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(errors), \
                patch.object(Path, "cwd", return_value=self.tmp):
            status = card_moves.main(["new-moves", *arguments])
        return status, out.getvalue(), errors.getvalue()

    def files(self) -> dict[str, bytes]:
        return {path.relative_to(self.tmp).as_posix(): path.read_bytes()
                for path in sorted((self.tmp / "scripts").rglob("*")) if path.is_file()}

    def test_a_fragment_is_named_with_the_current_utc_time_and_never_written_over(self) -> None:
        status, out, _ = self.run_new_moves("regroup-orders", "--base", "main")
        path = wiki.ROOT / cards.FRAGMENTS / "20261124T123005Z-regroup-orders.jsonl"
        self.assertEqual((status, path.read_bytes()), (0, b""))
        self.assertIn("scripts/card-moves.d/20261124T123005Z-regroup-orders.jsonl: add the change's rows to it", out)
        # Empty, it is no fragment yet: the check says so until the change's rows are in it.
        self.assertIn("scripts/card-moves.d/20261124T123005Z-regroup-orders.jsonl: no row",
                      card_moves.read_ledger(wiki.ROOT / "scripts")[1][0])
        path.write_text(json.dumps(self.added[0]) + "\n")
        # Another, in the same second: named one second later, so that it sorts after the first, which stays as it is.
        status, out, _ = self.run_new_moves("regroup-orders", "--base", "main")
        later = wiki.ROOT / cards.FRAGMENTS / "20261124T123006Z-regroup-orders.jsonl"
        self.assertEqual((status, path.read_text(), later.read_bytes()), (0, json.dumps(self.added[0]) + "\n", b""))
        # Without a base it can read (origin/main, by default, which this repository has not), it names none and
        # writes nothing, the folder of fragments included.
        shutil.rmtree(wiki.ROOT / cards.FRAGMENTS)
        status, out, errors = self.run_new_moves("regroup-orders")
        self.assertEqual((status, out, (wiki.ROOT / cards.FRAGMENTS).exists()), (1, "", False))
        self.assertIn("error: --base origin/main is no commit Git can read here", errors)
        for slug in ("Regroup", "-x", "a_b", "x.jsonl", ""):
            with self.subTest(slug=slug), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(self.run_new_moves(slug)[0], 2)

    def test_rows_appended_to_the_frozen_file_move_into_a_fragment(self) -> None:
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        frozen.write_text(self.published + "".join(json.dumps(row) + "\n" for row in self.added))
        status, out, errors = self.run_new_moves("late-moves", "--take-appended", "--base", "main")
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(frozen.read_text(), self.published)
        fragment = wiki.ROOT / cards.FRAGMENTS / "20261124T123005Z-late-moves.jsonl"
        self.assertEqual(fragment.read_text(), "".join(json.dumps(row) + "\n" for row in self.added))
        self.assertIn("2 rows taken from scripts/card-moves.jsonl, which is main's again", out)
        # The logical ledger has the same rows in the same order.
        files, problems = card_moves.read_ledger(wiki.ROOT / "scripts")
        self.assertEqual(problems, [])
        self.assertEqual([line for _, _, line in card_moves.ledger_rows(files)],
                         [self.published.strip(), *(json.dumps(row) for row in self.added)])

    def test_take_appended_needs_the_base_s_frozen_file_at_its_start(self) -> None:
        frozen = wiki.ROOT / "scripts" / cards.MOVES
        for text, message in ((self.published.replace(af(20), af(23)) + json.dumps(self.added[0]) + "\n",
                               "scripts/card-moves.jsonl at main is not the start of yours, byte for byte: rebase "
                               "first"),
                              (self.published, "has no row beyond main's; there is nothing to take")):
            with self.subTest(message=message):
                frozen.write_text(text)
                before = self.files()
                status, _, errors = self.run_new_moves("late-moves", "--take-appended", "--base", "main")
                self.assertEqual(status, 1)
                self.assertIn(message, errors)
                self.assertEqual(self.files(), before)
        # A base it cannot read is refused first, as by the other modes.
        status, _, errors = self.run_new_moves("late-moves", "--take-appended", "--base", "nowhere")
        self.assertEqual(status, 1)
        self.assertIn("error: --base nowhere is no commit Git can read here", errors)

    def test_a_new_fragment_takes_a_fresh_stamp_and_keeps_its_slug_and_bytes(self) -> None:
        folder = wiki.ROOT / cards.FRAGMENTS
        folder.mkdir()
        old = folder / "20260101T000000Z-p.jsonl"
        old.write_bytes(b'{"page": "a", "to": "b", "article_id": "af_000000000000000000000001"}')
        status, out, _ = self.run_new_moves("--restamp", "scripts/card-moves.d/20260101T000000Z-p.jsonl",
                                            "--base", "main")
        new = folder / "20261124T123005Z-p.jsonl"
        self.assertEqual((status, old.exists(), new.read_bytes()),
                         (0, False, b'{"page": "a", "to": "b", "article_id": "af_000000000000000000000001"}'))
        self.assertIn("scripts/card-moves.d/20260101T000000Z-p.jsonl -> scripts/card-moves.d/20261124T123005Z-p.jsonl",
                      out)
        # Already stamped now: nothing to do.
        self.assertEqual(self.run_new_moves("--restamp", str(new), "--base", "main")[0], 0)
        self.assertTrue(new.exists())
        # A fragment the base has keeps its name.
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "fragment")
        self.clock.stop()
        later = patch.object(card_moves, "utc_now", return_value=datetime(2026, 11, 25, tzinfo=timezone.utc))
        later.start()
        self.addCleanup(later.stop)
        status, _, errors = self.run_new_moves("--restamp", str(new), "--base", "main")
        self.assertEqual((status, new.exists()), (1, True))
        self.assertIn("is published at main; a published fragment keeps its name", errors)
        # Nor is anything but a fragment of the folder renamed, or one the base cannot be read for.
        for given in ("scripts/card-moves.jsonl", "scripts/card-moves.d/notes.txt", str(self.tmp / "x.jsonl")):
            with self.subTest(given=given):
                self.assertEqual(self.run_new_moves("--restamp", given, "--base", "main")[0], 1)
        self.assertIn("is no commit here", self.run_new_moves("--restamp", str(new), "--base", "nowhere")[2])


    def tree(self, *roots: Path) -> dict[str, tuple[str, object]]:
        """Every entry below ``roots``, links not followed: its kind and its bytes, or where it links to."""
        found = {}
        for root in roots:
            for folder, folders, names in os.walk(root, followlinks=False):
                for name in folders + names:
                    path = Path(folder) / name
                    mode = os.lstat(path).st_mode
                    found[str(path)] = (("link", os.readlink(path)) if stat.S_ISLNK(mode) else
                                        ("folder", None) if stat.S_ISDIR(mode) else ("file", path.read_bytes()))
        return found

    def test_a_name_taken_after_new_moves_looked_is_never_written_over_or_followed(self) -> None:
        # Another process takes the name new-moves chose, between its look at the fragments (fresh_name) and the
        # creation or the rename, with a file or with a link to a file outside: each mode refuses, and writes nothing,
        # there or outside; the file or link and what it links to stay as they were.
        scripts = wiki.ROOT / "scripts"
        frozen = scripts / cards.MOVES
        appended = (self.published + "".join(json.dumps(row) + "\n" for row in self.added)).encode()
        row = (json.dumps(self.added[0]) + "\n").encode()
        given = "scripts/card-moves.d/20260101T000000Z-p.jsonl"
        modes = {"new-moves": ("moved-pages", "--base", "main"),
                 "--take-appended": ("moved-pages", "--take-appended", "--base", "main"),
                 "--restamp": ("--restamp", given, "--base", "main")}
        looked = card_moves.fresh_name
        for kind in ("a file", "a link"):
            for mode, arguments in modes.items():
                with self.subTest(kind=kind, mode=mode):
                    outside = Path(tempfile.mkdtemp())
                    self.addCleanup(shutil.rmtree, outside)
                    (outside / "elsewhere.jsonl").write_bytes(row)
                    frozen.write_bytes(appended)
                    folder = scripts / "card-moves.d"
                    folder.mkdir()
                    (folder / "20260101T000000Z-p.jsonl").write_bytes(row)
                    taken = []

                    def racing(*parameters, **options):
                        name, problem = looked(*parameters, **options)
                        if kind == "a file":
                            (folder / name).write_bytes(b"another process's\n")
                        else:
                            (folder / name).symlink_to(outside / "elsewhere.jsonl")
                        taken.append(name)
                        return name, problem

                    try:
                        before = self.tree(self.tmp / "scripts", outside)
                        with patch.object(card_moves, "fresh_name", racing):
                            status, out, errors = self.run_new_moves(*arguments)
                        self.assertEqual((status, out), (1, ""))
                        self.assertIn(f"error: scripts/card-moves.d/{taken[0]} is there already", errors)
                        expected = {**before, str(folder / taken[0]): (
                            ("file", b"another process's\n") if kind == "a file"
                            else ("link", str(outside / "elsewhere.jsonl")))}
                        self.assertEqual(self.tree(self.tmp / "scripts", outside), expected)
                    finally:
                        shutil.rmtree(folder)

    def test_no_helper_writes_through_a_link_or_into_anything_but_a_folder(self) -> None:
        # Each helper, in each case, refuses before it creates, writes or renames anything, and writes nothing there or
        # outside the checkout: scripts/card-moves.d a link to a folder outside, or a file; scripts/ a link; for
        # --restamp, the fragment named a link; for --take-appended, the frozen file a link. The frozen file holds rows
        # beyond the base's, so that --take-appended has something to take. (A name new-moves chooses is no fragment's:
        # it sorts after every one; one taken meanwhile is the next test's.)
        scripts = wiki.ROOT / "scripts"
        frozen = scripts / cards.MOVES
        appended = (self.published + "".join(json.dumps(row) + "\n" for row in self.added)).encode()
        row = (json.dumps(self.added[0]) + "\n").encode()
        given = "scripts/card-moves.d/20260101T000000Z-p.jsonl"
        now = "20261124T123005Z"

        def fragments_link(outside: Path) -> None:
            (outside / "fragments").mkdir()
            (outside / "fragments" / "20260101T000000Z-p.jsonl").write_bytes(row)
            (scripts / "card-moves.d").symlink_to(outside / "fragments")

        def fragments_file(outside: Path) -> None:
            (scripts / "card-moves.d").write_bytes(row)

        def scripts_link(outside: Path) -> None:
            (scripts / "card-moves.d").mkdir()
            (scripts / "card-moves.d" / "20260101T000000Z-p.jsonl").write_bytes(row)
            scripts.rename(outside / "scripts")
            scripts.symlink_to(outside / "scripts")

        def name_link(outside: Path) -> None:
            (scripts / "card-moves.d").mkdir()
            (outside / "elsewhere.jsonl").write_bytes(row)
            (scripts / "card-moves.d" / "20260101T000000Z-p.jsonl").symlink_to(outside / "elsewhere.jsonl")

        def frozen_link(outside: Path) -> None:
            (outside / "frozen.jsonl").write_bytes(appended)
            frozen.unlink()
            frozen.symlink_to(outside / "frozen.jsonl")

        modes = {"new-moves": ("moved-pages", "--base", "main"),
                 "--take-appended": ("moved-pages", "--take-appended", "--base", "main"),
                 "--restamp": ("--restamp", given, "--base", "main")}
        cases = [
            ("scripts/card-moves.d a link to a folder outside", fragments_link, modes,
             {mode: "error: scripts/card-moves.d is no folder" for mode in modes}),
            ("scripts/card-moves.d a file", fragments_file, modes,
             {mode: "error: scripts/card-moves.d is no folder" for mode in modes}),
            ("scripts a link", scripts_link, modes, {mode: "error: scripts is no folder" for mode in modes}),
            ("the restamped fragment a link", name_link, {"--restamp": modes["--restamp"]},
             {"--restamp": f"error: {given} is no fragment in scripts/card-moves.d"}),
            ("the frozen file a link", frozen_link, {"--take-appended": modes["--take-appended"]},
             {"--take-appended": "error: scripts/card-moves.jsonl: no regular file"}),
        ]
        for label, make, runs, messages in cases:
            for mode, arguments in runs.items():
                with self.subTest(case=label, mode=mode):
                    outside = Path(tempfile.mkdtemp())
                    self.addCleanup(shutil.rmtree, outside)
                    frozen.write_bytes(appended)
                    try:
                        make(outside)
                        before = self.tree(self.tmp / "scripts", outside)
                        status, out, errors = self.run_new_moves(*arguments)
                        self.assertEqual((status, out), (1, ""))
                        self.assertIn(messages[mode], errors)
                        self.assertEqual(self.tree(self.tmp / "scripts", outside), before)
                    finally:
                        if scripts.is_symlink():
                            scripts.unlink()
                            (outside / "scripts").rename(scripts)
                        if frozen.is_symlink():
                            frozen.unlink()
                        fragments = scripts / "card-moves.d"
                        if fragments.is_symlink() or fragments.is_file():
                            fragments.unlink()
                        elif fragments.is_dir():
                            shutil.rmtree(fragments)
        # A file outside named as a fragment of the folder is no fragment of it, whatever the folder holds.
        outside = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, outside)
        (scripts / "card-moves.d").mkdir()
        for folder in (outside, scripts / "card-moves.d"):
            (folder / "20260101T000000Z-p.jsonl").write_bytes(row)
        before = self.tree(self.tmp / "scripts", outside)
        status, _, errors = self.run_new_moves("--restamp", str(outside / "20260101T000000Z-p.jsonl"), "--base", "main")
        self.assertEqual(status, 1)
        self.assertIn("is no fragment in scripts/card-moves.d", errors)
        self.assertEqual(self.tree(self.tmp / "scripts", outside), before)
        shutil.rmtree(scripts / "card-moves.d")
        # And once nothing refuses, each mode writes in the checkout only.
        frozen.write_bytes(appended)
        self.assertEqual(self.run_new_moves(*modes["--take-appended"])[0], 0)
        (scripts / "card-moves.d" / "20260101T000000Z-p.jsonl").write_bytes(row)
        self.assertEqual(self.run_new_moves(*modes["--restamp"])[0], 0)
        # The restamp names p one second after the fragment just taken, which sorts last.
        self.assertEqual(sorted(path.name for path in (scripts / "card-moves.d").iterdir()),
                         [f"{now}-moved-pages.jsonl", "20261124T123006Z-p.jsonl"])


class NewMovesEntryPoint(unittest.TestCase):
    """`python scripts/card_moves.py new-moves`, run as a script from a Git checkout of its own, with no root injected:
    each helper writes in the checkout it is run from, and refuses before it writes, changing nothing there or anywhere
    else, when scripts/ is a link to another checkout's scripts, or when the script run is another checkout's."""

    MODULES = ("card_moves.py",)
    PUBLISHED = json.dumps({"page": "Algebra/old", "to": "Algebra/p", "article_id": af(20)}) + "\n"
    ADDED = json.dumps({"page": "Algebra/older", "to": "Algebra/q", "article_id": af(21)}) + "\n"

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        self.environment = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "GIT_AUTHOR_NAME": "A", "GIT_AUTHOR_EMAIL":
                            "a@example.org", "GIT_COMMITTER_NAME": "A", "GIT_COMMITTER_EMAIL": "a@example.org"}

    def checkout(self, name: str) -> Path:
        """A Git checkout with the modules new-moves needs in scripts/ and a frozen file of one row, committed; and,
        uncommitted, a row added to the frozen file and a fragment, for --take-appended and --restamp."""
        root = self.tmp / name
        (root / "scripts").mkdir(parents=True)
        for module in self.MODULES:
            shutil.copyfile(Path(cards.__file__).resolve().parent / module, root / "scripts" / module)
        (root / "scripts" / cards.MOVES).write_text(self.PUBLISHED)
        for arguments in (("init", "-q", "-b", "main"), ("add", "-A"), ("commit", "-q", "-m", "base")):
            subprocess.run(["git", *arguments], cwd=root, check=True, env=self.environment)
        (root / "scripts" / cards.MOVES).write_text(self.PUBLISHED + self.ADDED)
        (root / cards.FRAGMENTS).mkdir()
        (root / cards.FRAGMENTS / "20260101T000000Z-p.jsonl").write_text(self.ADDED)
        return root

    def new_moves(self, cwd: Path, *arguments: str, script: str = "scripts/card_moves.py") -> tuple[int, str, str]:
        result = subprocess.run([sys.executable, script, "new-moves", *arguments, "--base", "main"], cwd=cwd,
                                capture_output=True, text=True, env=self.environment)
        return result.returncode, result.stdout, result.stderr

    MODES = {"new-moves": ("moved-pages",), "--take-appended": ("moved-pages", "--take-appended"),
             "--restamp": ("--restamp", "scripts/card-moves.d/20260101T000000Z-p.jsonl")}

    def test_each_helper_writes_in_the_checkout_it_is_run_from(self) -> None:
        for mode, arguments in self.MODES.items():
            with self.subTest(mode=mode):
                root = self.checkout(mode.strip("-"))
                status, out, errors = self.new_moves(root, *arguments)
                self.assertEqual((status, errors), (0, ""))
                names = sorted(path.name for path in (root / cards.FRAGMENTS).iterdir())
                stamp = r"\d{8}T\d{6}Z"
                if mode == "--restamp":
                    self.assertRegex(" ".join(names), rf"^{stamp}-p\.jsonl$")
                else:
                    self.assertEqual(len(names), 2)
                    self.assertRegex(names[1], rf"^{stamp}-moved-pages\.jsonl$")
                if mode == "--take-appended":
                    self.assertEqual((root / cards.FRAGMENTS / names[1]).read_text(), self.ADDED)
                    self.assertEqual((root / "scripts" / cards.MOVES).read_text(), self.PUBLISHED)

    def test_a_new_fragment_sorts_after_those_of_its_second_and_ahead_and_writes_over_none(self) -> None:
        # Fragments of the same slug, stamped from two seconds before the clock to half a minute after it, as the
        # required step lets a new fragment be: new-moves writes over none of them and names its fragment one second
        # after the latest, so that it sorts after every one.
        root = self.checkout("clash")
        now = datetime.now(timezone.utc).replace(microsecond=0)
        for offset in range(-2, 30):
            stamp = (now + timedelta(seconds=offset)).strftime(card_moves.STAMP)
            (root / cards.FRAGMENTS / f"{stamp}-moved-pages.jsonl").write_text(self.ADDED)
        before = entries(root)
        status, out, errors = self.new_moves(root, "moved-pages")
        made = f"{cards.FRAGMENTS}/{now + timedelta(seconds=30):%Y%m%dT%H%M%SZ}-moved-pages.jsonl"
        self.assertEqual((status, errors), (0, ""))
        self.assertTrue(out.startswith(f"{made}: add the change's rows to it"), out)
        self.assertEqual(entries(root), {**before, str(root / made): ("file", b"")})

    def test_no_helper_writes_through_another_checkout_s_scripts(self) -> None:
        # scripts/ of the checkout a link to the scripts/ of another checkout: the modules resolve their root to the
        # other checkout, and each helper refuses, changing neither. And the script of another checkout, run from
        # this one, refuses too.
        other = self.checkout("other")
        for mode, arguments in self.MODES.items():
            with self.subTest(mode=mode, case="a linked scripts/"):
                root = self.tmp / f"linked-{mode.strip('-')}"
                root.mkdir()
                subprocess.run(["git", "init", "-q", "-b", "main"], cwd=root, check=True, env=self.environment)
                (root / "scripts").symlink_to(other / "scripts")
                before = entries(root, other)
                status, out, errors = self.new_moves(root, *arguments)
                self.assertEqual((status, out), (1, ""))
                self.assertIn("error: scripts is no folder", errors)
                self.assertEqual(entries(root, other), before)
            with self.subTest(mode=mode, case="another checkout's script"):
                root = self.checkout(f"own-{mode.strip('-')}")
                before = entries(root, other)
                status, out, errors = self.new_moves(root, *arguments, script=str(other / "scripts" / "card_moves.py"))
                self.assertEqual((status, out), (1, ""))
                self.assertIn(f"is not the scripts/card_moves.py of the checkout it is run from, {root}", errors)
                self.assertEqual(entries(root, other), before)


def entries(*roots: Path) -> dict[str, tuple[str, object]]:
    """Every entry below ``roots``, links not followed, but Git's own folder: its kind and its bytes, or where it
    links to."""
    found = {}
    for root in roots:
        for folder, folders, names in os.walk(root, followlinks=False):
            folders[:] = [name for name in folders if name != ".git"]
            for name in folders + names:
                path = Path(folder) / name
                mode = os.lstat(path).st_mode
                found[str(path)] = (("link", os.readlink(path)) if stat.S_ISLNK(mode) else
                                    ("folder", None) if stat.S_ISDIR(mode) else ("file", path.read_bytes()))
    return found


class History:
    """A small wiki and a valid history of moves and retirements written forward as it happens, in two phases: what
    merged before the base commit (its rows go into published fragments) and what a change does since (its rows go into
    new fragments). The wiki: the folders A and A/g; plain and card folders below A/g, each with statement pages; and
    statement pages in A/g. The moves: a page to another plain folder; a folder, card or not, renamed with each of its
    pages; a statement retired for a live page or folder, or for a page that then moves into its address; a card
    retired for another card, its folder kept as a plain folder or dissolved, its pages moving out before or after; a
    page visiting a folder address and leaving it, right below the address or below a gone folder s that all deep
    visits to it share; and a folder moving, with its pages, into an address and later out of it. A page may visit an
    address before a folder comes, while it is there and after it left: one path, held at different times by folders
    that are not one."""

    ROOTS = {"A": 1, "A/g": 2}

    def __init__(self, rng: random.Random):
        self.rng = rng
        self.numbers = iter(range(100, 10 ** 6))
        self.names = iter(range(10 ** 6))
        self.folders = dict(self.ROOTS)
        self.pages: dict[str, int] = {}
        self.cards: dict[str, int] = {}
        # Folders whose card was retired and that stay, and pages a hand-off put at a retired statement's address:
        # neither moves again, as an address has one owner.
        self.kept: set[str] = set()
        self.fixed: set[str] = set()
        # Folder addresses a page visited, which no folder has moved into; those a folder moved into and holds (stops);
        # those it left. A folder moves into the first, a page visits any. The visits below each address, each with
        # whether a folder had come, held it or had left, and whether it was deep, below the shared gone folder s.
        self.transient: set[str] = set()
        self.stops: set[str] = set()
        self.passed: set[str] = set()
        self.visits: dict[str, list[tuple[str, bool]]] = defaultdict(list)
        self.arrived: set[str] = set()
        for _ in range(rng.randint(2, 3)):
            folder = self.name("A/g", "f")
            self.folders[folder] = next(self.numbers)
            members = [self.page(folder) for _ in range(rng.randint(1, 3))]
            if rng.random() < 0.6:
                self.cards[folder] = self.pages[members[0]]
        for _ in range(rng.randint(1, 3)):
            self.page("A/g")
        self.rows: list[dict] = []
        self.initial = self.state()

    def name(self, folder: str, prefix: str) -> str:
        return f"{folder}/{prefix}{next(self.names)}"

    def page(self, folder: str) -> str:
        address = self.name(folder, "p")
        self.pages[address] = next(self.numbers)
        return address

    def state(self) -> tuple[dict, dict, dict]:
        return dict(self.folders), dict(self.pages), dict(self.cards)

    def plain(self) -> list[str]:
        return sorted(folder for folder in self.folders if folder not in self.cards and folder != "A")

    def movable(self) -> list[str]:
        return sorted(page for page in self.pages
                      if page.rsplit("/", 1)[0] not in self.cards and page not in self.fixed)

    def step(self) -> None:
        """One operation, chosen among those whose preconditions hold."""
        for _ in range(20):
            if getattr(self, self.rng.choice(["move", "move", "rename", "retire", "retire", "hand_off",
                                             "card", "visit", "arrive", "depart", "occupy"]))():
                return

    def move(self) -> bool:
        pages = self.movable()
        if not pages:
            return False
        page = self.rng.choice(pages)
        new = self.name(self.rng.choice(self.plain()), "p")
        self.pages[new] = self.pages.pop(page)
        self.rows.append({"page": page, "to": new, "article_id": af(self.pages[new])})
        return True

    def rename(self) -> bool:
        folders = sorted(folder for folder in self.folders if folder.startswith("A/g/") and folder not in self.kept
                         and not any(page.startswith(f"{folder}/") for page in self.fixed))
        if not folders:
            return False
        folder = self.rng.choice(folders)
        self.rows += self.relocate(folder, self.name("A/g", "f"))
        # Renamed from an address it moved into, the folder has left it.
        if folder in self.stops:
            self.stops.discard(folder)
            self.passed.add(folder)
        return True

    def retire(self) -> bool:
        pages = self.movable()
        if len(pages) < 2:
            return False
        page = self.rng.choice(pages)
        number = self.pages.pop(page)
        targets = sorted(self.pages.values()) + sorted(self.folders[folder] for folder in self.folders
                                                       if folder != "A")
        self.rows.append({"statement": af(number), "page": page, "replaced_by": af(self.rng.choice(targets))})
        return True

    def hand_off(self) -> bool:
        pages = self.movable()
        if len(pages) < 2:
            return False
        page, successor = self.rng.sample(pages, 2)
        number = self.pages.pop(page)
        self.rows.append({"statement": af(number), "page": page, "replaced_by": af(self.pages[successor])})
        self.pages[page] = self.pages.pop(successor)
        self.fixed.add(page)
        self.rows.append({"page": successor, "to": page, "article_id": af(self.pages[page])})
        return True

    def visit(self) -> bool:
        """A page visits a folder address and leaves it for a plain folder: one a page visited before a folder came, one
        a folder holds, one a folder left, or a new one in a plain folder."""
        known = [(phase, folder) for phase, folders in (("before", self.transient), ("during", self.stops),
                                                        ("after", self.passed)) for folder in sorted(folders)]
        if known and self.rng.random() < 0.7:
            phase, folder = self.rng.choice(known)
        else:
            phase, folder = "before", self.name(self.rng.choice(self.plain()), "t")
            self.transient.add(folder)
        return self.pass_by(folder, phase)

    def pass_by(self, folder: str, phase: str) -> bool:
        """A page's two rows into an address below ``folder`` and out to a plain folder: right below it, or below its
        gone folder s, in a gone folder of its own."""
        pages = self.movable()
        if not pages:
            return False
        page = self.rng.choice(pages)
        deep = self.rng.random() < 0.5
        stop = self.name(self.name(f"{folder}/s", "e") if deep else folder, "p")
        self.visits[folder].append((phase, deep))
        new = self.name(self.rng.choice(self.plain()), "p")
        number = self.pages.pop(page)
        self.pages[new] = number
        self.rows += [{"page": page, "to": stop, "article_id": af(number)},
                      {"page": stop, "to": new, "article_id": af(number)}]
        return True

    def occupy(self) -> bool:
        """A folder's stay at a new address, with pages visiting below it before the folder comes, while it is there
        and after it leaves (if it leaves), each right below the address or below its gone folder s: in one step."""
        stop = self.name(self.rng.choice(self.plain()), "t")
        folders = self.movers(stop)
        if not folders:
            return False
        self.transient.add(stop)
        for _ in range(self.rng.randint(0, 2)):
            self.pass_by(stop, "before")
        self.come(self.rng.choice(folders), stop)
        for _ in range(self.rng.randint(0, 2)):
            self.pass_by(stop, "during")
        if stop in self.stops and self.rng.random() < 0.7:
            self.leave(stop)
            for _ in range(self.rng.randint(0, 2)):
                self.pass_by(stop, "after")
        return True

    def relocate(self, folder: str, new: str) -> list[dict]:
        """Move ``folder``, card or not, to ``new``, each of its pages with it: the rows."""
        number = self.folders.pop(folder)
        self.folders[new] = number
        if folder in self.cards:
            self.cards[new] = self.cards.pop(folder)
        rows = [{"folder": folder, "to": new, "article_id": af(number)}]
        for page in sorted(page for page in self.pages if page.rsplit("/", 1)[0] == folder):
            moved = f"{new}/{page.rsplit('/', 1)[1]}"
            self.pages[moved] = self.pages.pop(page)
            rows.append({"page": page, "to": moved, "article_id": af(self.pages[moved])})
        return rows

    def movers(self, stop: str) -> list[str]:
        """The folders that may move into ``stop``: in A/g, card or not, neither kept nor at a stop, holding no page a
        hand-off fixed, and not above ``stop``."""
        return sorted(folder for folder in self.folders if folder.startswith("A/g/") and folder not in self.kept
                      and folder not in self.stops and not stop.startswith(f"{folder}/")
                      and not any(page.startswith(f"{folder}/") for page in self.fixed))

    def arrive(self) -> bool:
        """A folder moves with its pages into an address a page visited, or a new one in A/g, where it stays until it
        departs or is renamed."""
        visited = sorted(self.transient)
        stop = self.rng.choice(visited) if visited and self.rng.random() < 0.6 else self.name("A/g", "t")
        folders = self.movers(stop)
        if not folders:
            return False
        self.come(self.rng.choice(folders), stop)
        return True

    def come(self, folder: str, stop: str) -> None:
        self.transient.discard(stop)
        self.rows += self.relocate(folder, stop)
        self.stops.add(stop)
        self.arrived.add(stop)

    def depart(self) -> bool:
        """A folder leaves an address it moved into for a new one in A/g, with its pages."""
        if not self.stops:
            return False
        self.leave(self.rng.choice(sorted(self.stops)))
        return True

    def leave(self, stop: str) -> None:
        self.rows += self.relocate(stop, self.name("A/g", "f"))
        self.stops.discard(stop)
        self.passed.add(stop)

    def card(self) -> bool:
        if len(self.cards) < 2:
            return False
        folder = self.rng.choice(sorted(self.cards))
        replacement = self.folders[self.rng.choice(sorted(set(self.cards) - {folder}))]
        retire = {"card": af(self.folders[folder]), "folder": folder, "replaced_by": af(replacement)}
        del self.cards[folder]
        # Retired, the card's folder stays at its address, kept or dissolved: no page visits it as a folder's stop.
        self.stops.discard(folder)
        if self.rng.random() < 0.5:
            # Declassified: a plain folder keeping its id, at an address that never moves again.
            self.kept.add(folder)
            self.rows.append(retire)
            return True
        moves = []
        for page in sorted(page for page in self.pages if page.rsplit("/", 1)[0] == folder):
            new = self.name(self.rng.choice([plain for plain in self.plain() if plain != folder]), "p")
            self.pages[new] = self.pages.pop(page)
            moves.append({"page": page, "to": new, "article_id": af(self.pages[new])})
        del self.folders[folder]
        self.rows += [retire, *moves] if self.rng.random() < 0.5 else [*moves, retire]
        return True


class FragmentOrder(unittest.TestCase):
    """A seeded property test of the fragment guard (card_moves.guard) against the checks and the resolver: for
    generated valid histories, each split into fragments, published ones (the base's) and new ones, in which the guard
    finds every pair it judges (each new fragment with each other and with each published one) independent, every order
    of the fragments that keeps the published ones in the order they merged gives the same check results (check_moves,
    reconcile included, and the snapshot alone) and the same history() table of every old address. Each history's table
    also gives every address a row speaks of, and every gone folder that none speaks of, the endpoint that the history,
    followed forward, gives it (spoken, fallen). Sampling shows no counterexample among the cases drawn; it does not
    prove that independent fragments commute in general."""

    SEED = 20261124
    CASES = 400
    SPLITS = 4

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        vault = self.tmp / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(card_moves, "ROOT", self.tmp),
                    patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"),
                    patch.object(cards.sync, "LINKS", vault / "links")):
            one.start()
            self.addCleanup(one.stop)
        self.hook = load_hook()
        self.trees: dict = {}

    @staticmethod
    def annotations(state: tuple[dict, dict, dict]) -> dict[Path, dict]:
        folders, pages, card_mains = state
        found = {}
        for folder, number in folders.items():
            row = {"id": af(number)}
            if folder in card_mains:
                row["extensions"] = {"org.atlas-wiki": {"card": {
                    "kind": "result", "main_article_id": af(card_mains[folder]), "importance": "key",
                    "level": "undergraduate"}}}
            found[(wiki.ROADMAP / folder / "README.md").resolve()] = row
        for page, number in pages.items():
            found[(wiki.ROADMAP / f"{page}.md").resolve()] = {"id": af(number)}
        return found

    def lay_out(self, state: tuple[dict, dict, dict]) -> None:
        shutil.rmtree(wiki.ROADMAP, ignore_errors=True)
        folders, pages, _ = state
        for folder in folders:
            (wiki.ROADMAP / folder).mkdir(parents=True, exist_ok=True)
            (wiki.ROADMAP / folder / "README.md").write_text("# folder\n")
        for page in pages:
            (wiki.ROADMAP / f"{page}.md").write_text("# page\n")

    def outcome(self, order: list[tuple[str, list[dict]]], published: set[str], base_state, final_state) -> tuple:
        """The check results and the resolution of the ledger whose fragments are ``order`` (slug, rows), stamped in
        that order, with the slugs of ``published`` in the base."""
        files = [(cards.FROZEN, b"")]
        for position, (slug, rows) in enumerate(order):
            files.append((f"{cards.FRAGMENTS}/2020010{position + 1}T000000Z-{slug}.jsonl",
                          "".join(json.dumps(row) + "\n" for row in rows).encode()))
        base = card_moves.BaseLedger({path: card_moves.blob_id(data) for path, data in files
                                 if path == cards.FROZEN or path.rsplit("-", 1)[1][:-6] in published},
                                dict(files))
        annotations = self.annotations(final_state)
        found = cards.card_folders(annotations)
        strip = re.compile(r"\d{8}T\d{6}Z-")
        checked = sorted(strip.sub("", error) for error in cards.check_moves(
            annotations, found, base=base, base_annotations=self.annotations(base_state), renames=[], files=files))
        snapshot = sorted(strip.sub("", error) for error in cards.check_moves(annotations, found, files=files))
        # The required check's errors, with its own read of the live folders, are the moves check's that need no tree,
        # with the base and without.
        for known in (base, None):
            self.assertEqual(required_check(self.tmp, files, known, self.trees),
                             tree_free(cards.check_moves(annotations, found, base=known, files=files)))
        rows = [row for _, data in files for row in cards.parse_ledger_rows(data)]
        by_id = {af(number): (kind, address) for kind, table in (("folder", final_state[0]), ("page", final_state[1]))
                 for address, number in table.items()}
        replacements = {final: by_id[final] for final in cards.final_replacements(rows).values() if final in by_id}
        entries = [{"id": address, "kind": "node", "route": f"../roadmap/{address}.html", "title": address}
                   for address in final_state[1]]
        entries += [{"id": address, "kind": "scope", "route": f"../roadmap/{address}/index.html", "title": address}
                    for address in final_state[0]]
        entries.append({"id": "roadmap", "kind": "scope", "route": "../roadmap/index.html", "title": "roadmap"})
        pages = self.hook.Pages(self.hook.read_index({"schema": self.hook.INDEX_SCHEMA, "nodes": entries}))
        # A table, never an error: the history is valid, so the site resolves every address of it.
        table = sorted(self.hook.history(self.hook.read_ledger([(path, data.decode()) for path, data in files]),
                                         pages, replacements).items())
        return checked, snapshot, table

    @staticmethod
    def spoken(rows: list[dict], final_state: tuple[dict, dict, dict]) -> dict[tuple[str, str], str]:
        """Every old address a row speaks of that the site no longer publishes, by kind, with where its article ended,
        followed forward: the address the article has at the end, or, retired, the one its final replacement has. A
        retired statement's address that holds its replacement leads to itself."""
        folders, pages, _ = final_state
        at = {af(number): address for table in (folders, pages) for address, number in table.items()}
        final = cards.final_replacements(rows)
        found = {}
        for row in rows:
            kind = card_moves.row_kind(row)
            if kind in ("page", "folder"):
                # A card retired with its folder kept, a plain folder now, is still that folder.
                address, article = row[kind], row["article_id"]
                if article not in at:
                    article = final[("statement" if kind == "page" else "card", article)]
            else:
                address, article = row["folder" if kind == "card" else "page"], final[(kind, row[kind])]
                kind = "folder" if kind == "card" else "page"
            if address not in (folders if kind == "folder" else pages) or kind == "page" and "statement" in row:
                found[(kind, address)] = at[article]
        return found

    @staticmethod
    def fallen(rows: list[dict], initial_state: tuple[dict, dict, dict], final_state: tuple[dict, dict, dict],
               table: dict[tuple[str, str], str], spoken: dict[tuple[str, str], str]) -> dict[tuple[str, str], str]:
        """Every gone folder ``table`` gives a route and no row speaks of, with where the history, followed forward,
        says it leads: where the folder that held its nearest held ancestor led, just before the first row that left an
        address below it: that folder's address at the end, or, retired, its final replacement's. A folder holds an
        address from the base, or from the row that moves it there, until the row that moves it away; no other row
        changes what holds an address."""
        holding = dict(initial_state[0])
        before = []
        for row in rows:
            before.append(dict(holding))
            if card_moves.row_kind(row) == "folder":
                holding[row["to"]] = holding.pop(row["folder"])
        at = {af(number): address for address, number in final_state[0].items()}
        final = cards.final_replacements(rows)
        left = [row.get("page") if card_moves.row_kind(row) in ("page", "statement") else row["folder"] for row in rows]
        found = {}
        for kind, address in table:
            if kind != "folder" or (kind, address) in spoken:
                continue
            first = next(number for number, old in enumerate(left) if old.startswith(f"{address}/"))
            parts = address.split("/")
            above = next("/".join(parts[:depth]) for depth in range(len(parts) - 1, 0, -1)
                         if "/".join(parts[:depth]) in before[first])
            article = af(before[first][above])
            found[(kind, address)] = at[article] if article in at else at[final[("card", article)]]
        return found

    @staticmethod
    def split(rng: random.Random, rows: list[dict], parts: int, prefix: str) -> list[tuple[str, list[dict]]]:
        """``rows`` dealt into ``parts`` fragments, each keeping their order, none empty."""
        while True:
            dealt = [rng.randrange(parts) for _ in rows]
            if len(set(dealt)) == parts:
                return [(f"{prefix}{part}", [row for row, at in zip(rows, dealt) if at == part])
                        for part in range(parts)]

    @staticmethod
    def merged_in_turn(rng: random.Random, rows: list[dict], parts: int) -> list[tuple[str, list[dict]]]:
        """``rows``, the history before the base, as ``parts`` published fragments: each merged in its turn, valid on
        what merged before it, so each holds the rows that follow the last one's."""
        cuts = sorted(rng.sample(range(1, len(rows)), parts - 1))
        return [(f"g{part}", rows[start:end]) for part, (start, end) in enumerate(zip([0, *cuts], [*cuts, len(rows)]))]

    @staticmethod
    def orders(published: list, fresh: list) -> list[list]:
        """Every order of the fragments that keeps the published ones in the order they merged."""
        found = []
        for permutation in itertools.permutations(published + fresh):
            if [item for item in permutation if item in published] == published:
                found.append(list(permutation))
        return found

    def test_independent_fragments_give_one_outcome_in_every_order(self) -> None:
        rng = random.Random(self.SEED)
        counts = Counter()
        for case in range(self.CASES):
            history = History(rng)
            for _ in range(rng.randint(0, 3)):
                history.step()
            merged = list(history.rows)
            base_state = history.state()
            for _ in range(rng.randint(1, 4)):
                history.step()
            fresh_rows = history.rows[len(merged):]
            final_state = history.state()
            if not fresh_rows:
                continue
            self.lay_out(final_state)
            counts["histories"] += 1
            for row in history.rows:
                counts[f"rows: {card_moves.row_kind(row)}"] += 1
            reused = False
            sides = set()
            for folder, visits in history.visits.items():
                if folder not in history.arrived:
                    continue
                reused = True
                for deep in (False, True):
                    phases = {phase for phase, below in visits if below or not deep}
                    for pair, side in (({"before", "during"}, "its arrival"), ({"during", "after"}, "its departure"),
                                       ({"before", "after"}, "its stay")):
                        if pair <= phases:
                            sides.add(f"histories with {'deep ' if deep else ''}visits below an address on both sides "
                                      f"of {side}")
            for side in sides:
                counts[side] += 1
            counts["histories with an address held at different times by folders that are not one"] += reused
            # The history as written: valid, in one published fragment and one new one.
            authored = [("merged", merged)] if merged else []
            as_written = self.outcome([*authored, ("new", fresh_rows)], {"merged"}, base_state, final_state)
            self.assertEqual((as_written[0], as_written[1]), ([], []), (case, history.rows))
            # Every address a row speaks of leads where the history, followed forward, says its article ended: its
            # address at the end, or its final replacement's; never a fallback.
            spoken = self.spoken(history.rows, final_state)
            table = {tuple(key): endpoint for key, endpoint in as_written[2]}
            self.assertEqual({key: table.get(key) for key in spoken}, spoken, (case, history.rows))
            counts["routes a row says, checked against the history followed forward"] += len(spoken)
            # And every gone folder that no row speaks of leads where what held the address above it led, when the
            # history first left an address below it.
            fallen = self.fallen(history.rows, history.initial, final_state, table, spoken)
            self.assertEqual({key: table[key] for key in fallen}, fallen, (case, history.rows))
            counts["routes of gone folders no row speaks of, checked against the history followed forward"] += (
                len(fallen))
            for _ in range(self.SPLITS):
                published = self.merged_in_turn(rng, merged, rng.randint(1, min(2, len(merged)))) if merged else []
                fresh = self.split(rng, fresh_rows, rng.randint(1, min(3, len(fresh_rows))), "f")
                counts["splits"] += 1
                stable = card_moves.stable_folders([card_moves.LedgerRow("x", 1, row) for row in history.rows],
                                                   cards.LiveFolders())
                prints = {slug: card_moves.footprint([card_moves.LedgerRow(slug, 1, row) for row in rows], stable)
                          for slug, rows in published + fresh}
                pairs = [(one, two) for one, two in itertools.combinations([slug for slug, _ in fresh], 2)]
                pairs += [(one, two) for one, _ in fresh for two, _ in published]
                if any(card_moves.interaction(prints[one], prints[two]) for one, two in pairs):
                    counts["splits the guard declines"] += 1
                    continue
                counts["splits judged independent"] += 1
                counts["splits judged independent, of histories with such an address"] += reused
                counts[f"independent splits of {len(published)} published and {len(fresh)} new fragments"] += 1
                outcomes = set()
                orders = self.orders(published, fresh)
                for order in orders:
                    outcome = self.outcome(order, {slug for slug, _ in published}, base_state, final_state)
                    outcomes.add(json.dumps(outcome))
                    counts["orders checked"] += 1
                    counts["orders checked of independent splits with more than one order"] += len(orders) > 1
                    counts["orders checked, of histories with such an address"] += reused
                self.assertEqual(len(outcomes), 1, (case, history.rows, published, fresh, outcomes))
                self.assertEqual(json.loads(outcomes.pop())[:2], [[], []], (case, history.rows))
        report = "".join(f"\n  {key}: {value}" for key, value in sorted(counts.items()))
        print(f"\nseed {self.SEED}, {self.CASES} cases drawn:{report}", file=sys.stderr)
        # Both classes of pairs, published and new, and new and new, in interleavings of two and of three fragments.
        for kinds in ((1, 1), (0, 2), (2, 1), (1, 2), (0, 3)):
            self.assertGreater(counts[f"independent splits of {kinds[0]} published and {kinds[1]} new fragments"], 0)
        self.assertGreater(counts["splits the guard declines"], 0)
        # Visits on both sides of a folder's arrival and of its departure, deep ones too, among histories split
        # independently too.
        for side in ("its arrival", "its departure"):
            self.assertGreater(counts[f"histories with deep visits below an address on both sides of {side}"], 0)
        self.assertGreater(counts["splits judged independent, of histories with such an address"], 0)


class ChronologyControls(unittest.TestCase):
    """Independent controls of the ledger's chronology, each a history written forward as it happened, in a small
    roadmap: Topic, with the folder live, the card replacement (3) and its main page, and the card old (4) holding the
    pages p (21) and q (20). For each history: the moves check with the base (`moves --base`: the combined ledger and
    the base's file map, no replay since the base), and against it the required check's own (`card_moves.py check
    --base`: card_moves.check with its own read of the live folders, from Git's tree entries), which gives its errors
    but those that need the tree; the card check's (`check --base-ledger`: the same and the replay), the snapshot
    alone, the guard, and the hook's typed endpoints and generated links, all compared with what the history says,
    written down by hand."""

    TOPIC, LIVE, REPLACEMENT, OLD = "Topic", "Topic/live", "Topic/replacement", "Topic/old"
    FIXED = {"Topic": ("folder", 1), "Topic/live": ("folder", 2), "Topic/replacement": ("card", 3),
             "Topic/replacement/main": ("page", 7)}

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        vault = self.tmp / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(card_moves, "ROOT", self.tmp),
                    patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"),
                    patch.object(cards.sync, "LINKS", vault / "links")):
            one.start()
            self.addCleanup(one.stop)
        self.hook = load_hook()
        self.trees: dict = {}

    @staticmethod
    def move(kind: str, number: int, old: str, new: str) -> dict:
        return {kind: old, "to": new, "article_id": af(number)}

    @staticmethod
    def retire(kind: str, number: int, address: str, successor: int) -> dict:
        return {kind: af(number), "folder" if kind == "card" else "page": address, "replaced_by": af(successor)}

    @staticmethod
    def annotations(state: dict[str, tuple[str, int]]) -> dict[Path, dict]:
        found = {}
        for path, (kind, number) in state.items():
            page = wiki.ROADMAP / (f"{path}/README.md" if kind in ("card", "folder") else f"{path}.md")
            row: dict = {"id": af(number)}
            if kind == "card":
                main = next((value for name, (what, value) in state.items()
                             if what == "page" and name.rpartition("/")[0] == path), 999)
                row["extensions"] = {cards.OWN: {"card": {"kind": "result", "level": "graduate", "importance": "key",
                                                          "main_article_id": af(main)}}}
            found[page] = row
        return found

    def history(self, base: dict, end: dict, groups: list[list[dict]], published: int = 0) -> dict:
        """The checks of the ledger whose fragments are ``groups``, in that order, the first ``published`` of them the
        base's, from the base state ``base`` to the end state ``end``, and what the hook makes of it."""
        shutil.rmtree(wiki.ROADMAP, ignore_errors=True)
        annotations = self.annotations(end)
        for page in annotations:
            page.parent.mkdir(parents=True, exist_ok=True)
            page.write_text("# Page\n")
        files = [(cards.FROZEN, b"")] + [
            (f"{cards.FRAGMENTS}/2020010{number}T000000Z-part{number}.jsonl",
             "".join(json.dumps(row) + "\n" for row in rows).encode()) for number, rows in enumerate(groups, 1)]
        known = dict(files[:1 + published])
        ledger = card_moves.BaseLedger({path: card_moves.blob_id(data) for path, data in known.items()}, known)
        found = cards.card_folders(annotations)
        rows = [card_moves.LedgerRow(path, number, row) for path, data in files
                for number, row in enumerate(cards.parse_ledger_rows(data), 1)]
        fresh = [path for path, _ in files if path not in known]
        entries = [{"id": name, "kind": "node" if kind == "page" else "scope",
                    "route": f"../roadmap/{name}.html" if kind == "page" else f"../roadmap/{name}/index.html",
                    "title": name} for name, (kind, _) in end.items()]
        entries.append({"id": "roadmap", "kind": "scope", "route": "../roadmap/index.html", "title": "Roadmap"})
        pages = self.hook.Pages(self.hook.read_index({"schema": self.hook.INDEX_SCHEMA, "nodes": entries}))
        replacements = {af(number): ("page" if kind == "page" else "folder", name)
                        for name, (kind, number) in end.items()}
        read = self.hook.read_ledger([(path, data.decode()) for path, data in files])
        result = {"moves": cards.check_moves(annotations, found, base=ledger, files=files),
                  "strict": cards.check_moves(annotations, found, base=ledger,
                                              base_annotations=self.annotations(base), renames=[], files=files),
                  "snapshot": cards.check_moves(annotations, found, files=files),
                  "guard": card_moves.guard(rows, fresh, set(known) - {cards.FROZEN}, cards.LiveFolders()),
                  "required": required_check(self.tmp, files, ledger, self.trees)}
        self.assertEqual(result["required"], tree_free(result["moves"]))
        try:
            result["targets"] = {f"{kind}:{address}": endpoint for (kind, address), endpoint
                                 in self.hook.history(read, pages, replacements).items()}
            site = self.hook.Site()
            self.hook.redirects(site, read, pages, replacements, self.tmp / "docs")
            result["links"] = {path: (text.split('<p><a href="', 1)[1].split('"', 1)[0], "http-equiv" in text,
                                      RedirectElements.of(text))
                               for path, text in site.files.items() if path.endswith(".md")}
            result["table"] = (json.loads(site.files[self.hook.SCRIPT].split("var moves = ", 1)[1].split(", own = ")[0])
                               if self.hook.SCRIPT in site.files else {})
        except self.hook.CardDataError as error:
            result["targets"] = str(error)
        return result

    def base_with_old(self) -> tuple[dict, dict]:
        start = {**self.FIXED, "Topic/old": ("card", 4), "Topic/old/q": ("page", 20), "Topic/old/p": ("page", 21)}
        end = {**self.FIXED, "Topic/live/q": ("page", 20), "Topic/live/p": ("page", 21)}
        return start, end

    def test_an_inferred_subfolder_follows_its_card_s_retirement_in_every_order(self) -> None:
        # p moves into old/sub, a folder no snapshot has, and out to live; q moves out to live; the card old is retired
        # for replacement. Every order that keeps p's two moves in order passes every check, and old and old/sub, gone,
        # both lead to replacement: old/sub was in old, which leads there.
        start, end = self.base_with_old()
        enter = self.move("page", 21, "Topic/old/p", "Topic/old/sub/p")
        leave = self.move("page", 21, "Topic/old/sub/p", "Topic/live/p")
        sibling = self.move("page", 20, "Topic/old/q", "Topic/live/q")
        retire = self.retire("card", 4, "Topic/old", 3)
        expected_targets = {"folder:Topic/old": "Topic/replacement", "folder:Topic/old/sub": "Topic/replacement",
                            "page:Topic/old/p": "Topic/live/p", "page:Topic/old/sub/p": "Topic/live/p",
                            "page:Topic/old/q": "Topic/live/q"}
        expected_links = {
            "roadmap/Topic/old/p.md": ("../live/p.html", True, []),
            "roadmap/Topic/old/sub/p.md": ("../../live/p.html", True, []),
            "roadmap/Topic/old/q.md": ("../live/q.html", True, []),
            "roadmap/Topic/old/README.md": ("../replacement/index.html", False,
                                            [("p", "../live/p.html"), ("q", "../live/q.html")]),
            "roadmap/Topic/old/sub/README.md": ("../../replacement/index.html", False, [("p", "../../live/p.html")]),
            "dependencies/scopes/Topic/old.md": ("../../../roadmap/Topic/replacement/index.html", True, []),
            "dependencies/scopes/Topic/old/sub.md": ("../../../../roadmap/Topic/replacement/index.html", True, [])}
        expected_table = {"Topic/old": "Topic/replacement", "Topic/old/sub": "Topic/replacement",
                          "Topic/old/p": "Topic/live/p", "Topic/old/sub/p": "Topic/live/p",
                          "Topic/old/q": "Topic/live/q"}
        orders = [order for order in itertools.permutations((enter, leave, sibling, retire))
                  if order.index(enter) < order.index(leave)]
        self.assertEqual(len(orders), 12)
        for order in orders:
            with self.subTest(order=[next(iter(row.values())) for row in order]):
                found = self.history(start, end, [list(order)])
                self.assertEqual((found["moves"], found["strict"], found["snapshot"]), ([], [], []))
                self.assertEqual((found["targets"], found["links"], found["table"]),
                                 (expected_targets, expected_links, expected_table))

    def test_an_inferred_chain_two_folders_deep_follows_the_retirement(self) -> None:
        # r moves into old/sub/deeper, which the replay infers from old/sub, which it infers from old: the retirement of
        # old reaches both.
        start, end = self.base_with_old()
        start, end = {**start, "Topic/old/r": ("page", 22)}, {**end, "Topic/live/r": ("page", 22)}
        rows = [self.move("page", 21, "Topic/old/p", "Topic/old/sub/p"),
                self.move("page", 22, "Topic/old/r", "Topic/old/sub/deeper/r"), self.retire("card", 4, "Topic/old", 3),
                self.move("page", 22, "Topic/old/sub/deeper/r", "Topic/live/r"),
                self.move("page", 21, "Topic/old/sub/p", "Topic/live/p"),
                self.move("page", 20, "Topic/old/q", "Topic/live/q")]
        found = self.history(start, end, [rows])
        self.assertEqual((found["moves"], found["strict"], found["snapshot"]), ([], [], []))
        for folder in ("Topic/old", "Topic/old/sub", "Topic/old/sub/deeper"):
            self.assertEqual(found["targets"][f"folder:{folder}"], "Topic/replacement")
        self.assertEqual(found["links"]["roadmap/Topic/old/sub/deeper/README.md"],
                         ("../../../replacement/index.html", False, [("r", "../../../live/r.html")]))
        self.assertEqual(found["links"]["dependencies/scopes/Topic/old/sub/deeper.md"],
                         ("../../../../../roadmap/Topic/replacement/index.html", True, []))

    def test_a_folder_that_a_row_says_or_the_site_has_keeps_its_own_fallbacks(self) -> None:
        # live/sub, gone, rested on live, which the site has: the retirement of old, elsewhere, leaves it alone; and a
        # folder below old that a folder row placed keeps where that row leads.
        start, end = self.base_with_old()
        start = {**start, "Topic/live/sub/s": ("page", 23), "Topic/old/kept": ("folder", 30)}
        end = {**end, "Topic/live/s": ("page", 23), "Topic/kept": ("folder", 30)}
        rows = [self.move("page", 23, "Topic/live/sub/s", "Topic/live/s"),
                self.move("folder", 30, "Topic/old/kept", "Topic/kept"),
                self.move("page", 21, "Topic/old/p", "Topic/live/p"),
                self.move("page", 20, "Topic/old/q", "Topic/live/q"), self.retire("card", 4, "Topic/old", 3)]
        for order in (rows, rows[::-1][1:] + rows[-1:]):
            found = self.history(start, end, [list(order)])
            self.assertEqual(found["targets"]["folder:Topic/live/sub"], "Topic/live")
            self.assertEqual(found["targets"]["folder:Topic/old/kept"], "Topic/kept")
            self.assertEqual(found["targets"]["folder:Topic/old"], "Topic/replacement")

    def test_a_move_into_an_address_builds_only_on_the_retirement_that_freed_it(self) -> None:
        # X (10) moves from first to second, a free address; X is retired there for Y (11), in place; Y is retired there
        # for Z (12) at result. Each step is valid on the one before, published; the move into second built on no
        # retirement, so the later ones never make it misordered, as published history, as three new fragments or as
        # one fragment. As three new fragments the guard declines them, as it declines any two new fragments that
        # touch one address; in one fragment the card check refuses only that Y, made in the change, was no statement
        # page at its base, its own rule.
        start = {"T": ("folder", 1), "T/first": ("page", 10), "T/result": ("page", 12)}
        steps = [{"T": ("folder", 1), "T/second": ("page", 10), "T/result": ("page", 12)},
                 {"T": ("folder", 1), "T/second": ("page", 11), "T/result": ("page", 12)},
                 {"T": ("folder", 1), "T/result": ("page", 12)}]
        rows = [self.move("page", 10, "T/first", "T/second"), self.retire("statement", 10, "T/second", 11),
                self.retire("statement", 11, "T/second", 12)]
        before = start
        for number, after in enumerate(steps, 1):
            found = self.history(before, after, [[row] for row in rows[:number]], published=number - 1)
            self.assertEqual((found["moves"], found["strict"], found["snapshot"], found["guard"]), ([], [], [], []))
            before = after
        self.assertEqual(found["targets"], {"page:T/first": "T/result", "page:T/second": "T/result"})
        for groups in ([[row] for row in rows], [rows]):
            found = self.history(start, steps[-1], groups)
            self.assertEqual(found["snapshot"], [])
            self.assertFalse(any("builds on" in error for check in ("moves", "strict") for error in found[check]))
            self.assertEqual(found["targets"], {"page:T/first": "T/result", "page:T/second": "T/result"})
        self.assertEqual(found["moves"], [])
        self.assertEqual(found["strict"], [f"{cards.FRAGMENTS}/20200101T000000Z-part1.jsonl:3: {af(11)} was no "
                                           "statement page at the base commit"])
        found = self.history(start, steps[-1], [[row] for row in rows])
        self.assertEqual(len(found["guard"]), 3)
        self.assertTrue(all("both new, touch the address T/second" in error for error in found["guard"]))
        # A move into an address before the retirement of the occupant that freed it for the mover is refused, by every
        # check: W (13) at second is retired for X, which moves in.
        start = {"T": ("folder", 1), "T/second": ("page", 13), "T/first": ("page", 10)}
        end = {"T": ("folder", 1), "T/second": ("page", 10)}
        handoff = [self.retire("statement", 13, "T/second", 10), self.move("page", 10, "T/first", "T/second")]
        found = self.history(start, end, [handoff])
        self.assertEqual((found["moves"], found["strict"], found["snapshot"]), ([], [], []))
        found = self.history(start, end, [handoff[::-1]])
        reason = (f"{cards.FRAGMENTS}/20200101T000000Z-part1.jsonl:1: it builds on line 2, below it; a file's rows "
                  "come in the order they happened")
        for check in ("moves", "strict", "snapshot"):
            self.assertIn(reason, found[check], check)

    def test_a_statement_s_address_is_handed_to_a_folder_only_after_its_retirement(self) -> None:
        # The statement X (10) at T/p is retired for the folder Y (11), which then moves to T/p: a page and a folder of
        # one name share one address. The reverse order is refused by every check, for the same reason.
        start = {"T": ("folder", 1), "T/p": ("page", 10), "T/original": ("folder", 11)}
        end = {"T": ("folder", 1), "T/p": ("folder", 11)}
        before = self.retire("statement", 10, "T/p", 11)
        after = self.move("folder", 11, "T/original", "T/p")
        found = self.history(start, end, [[before, after]])
        self.assertEqual((found["moves"], found["strict"], found["snapshot"]), ([], [], []))
        self.assertEqual(found["targets"], {"folder:T/original": "T/p", "page:T/p": "T/p"})
        reason = (f"{cards.FRAGMENTS}/20200101T000000Z-part1.jsonl:1: it builds on line 2, below it; a file's rows "
                  "come in the order they happened")
        found = self.history(start, end, [[after, before]])
        for check in ("moves", "strict", "snapshot"):
            self.assertIn(reason, found[check], check)
        self.assertIn(f"{cards.FRAGMENTS}/20200101T000000Z-part1.jsonl:1: T/p already holds another article",
                      found["strict"])
        # As two fragments, the later one built on: the same reason, with its fix.
        found = self.history(start, end, [[after], [before]])
        for check in ("moves", "strict", "snapshot"):
            later = f"{cards.FRAGMENTS}/20200102T000000Z-part2.jsonl"
            self.assertTrue(any(error.startswith(f"{cards.FRAGMENTS}/20200101T000000Z-part1.jsonl:1: it builds on "
                                                 f"{later}, which sorts after it") for error in found[check]),
                            (check, found[check]))

    def test_a_card_s_address_is_never_handed_to_a_page(self) -> None:
        # A card is replaced by a card only, so no page takes a retired card's address: in either order, every check
        # refuses it, for the same reason.
        start = {**self.FIXED, "Topic/c": ("card", 4), "Topic/c/m": ("page", 21), "Topic/s": ("page", 10)}
        end = {**self.FIXED, "Topic/live/m": ("page", 21), "Topic/c": ("page", 10)}
        rows = [self.move("page", 21, "Topic/c/m", "Topic/live/m"), self.retire("card", 4, "Topic/c", 3),
                self.move("page", 10, "Topic/s", "Topic/c")]
        reason = f"{cards.MOVES}: the retired card {af(4)}'s address Topic/c is held by another article"
        for order in (rows, rows[::-1]):
            found = self.history(start, end, [list(order)])
            for check in ("moves", "strict", "snapshot"):
                self.assertIn(reason, found[check], check)

    def test_two_hops_and_a_retirement_chain_reach_their_endpoints(self) -> None:
        # The card old moves to middle and on to later with its pages; q leaves for live; p is retired for the card,
        # which is retired for replacement. A page added at replacement later gets no old address.
        start, _ = self.base_with_old()
        end = {**self.FIXED, "Topic/live/q": ("page", 20), "Topic/replacement/new": ("page", 90)}
        rows = [self.move("folder", 4, "Topic/old", "Topic/middle"),
                self.move("page", 21, "Topic/old/p", "Topic/middle/p"),
                self.move("page", 20, "Topic/old/q", "Topic/middle/q"),
                self.move("folder", 4, "Topic/middle", "Topic/later"),
                self.move("page", 21, "Topic/middle/p", "Topic/later/p"),
                self.move("page", 20, "Topic/middle/q", "Topic/live/q"),
                self.retire("statement", 21, "Topic/later/p", 4), self.retire("card", 4, "Topic/later", 3)]
        found = self.history(start, end, [rows])
        self.assertEqual((found["moves"], found["strict"], found["snapshot"]), ([], [], []))
        self.assertEqual(found["targets"], {
            **{f"folder:{name}": "Topic/replacement" for name in ("Topic/old", "Topic/middle", "Topic/later")},
            **{f"page:{name}/p": "Topic/replacement" for name in ("Topic/old", "Topic/middle", "Topic/later")},
            "page:Topic/old/q": "Topic/live/q", "page:Topic/middle/q": "Topic/live/q"})

    def test_sibling_moves_in_separate_fragments_resolve_alike_in_every_order(self) -> None:
        start = {"Topic": ("folder", 1), "Topic/live": ("folder", 2), "Topic/replacement": ("folder", 3)}
        end = dict(start)
        moves = []
        for number in range(3):
            start[f"Topic/live/{number}"] = ("page", 100 + number)
            end[f"Topic/replacement/{number}"] = ("page", 100 + number)
            moves.append(self.move("page", 100 + number, f"Topic/live/{number}", f"Topic/replacement/{number}"))
        for order in itertools.permutations(moves):
            found = self.history(start, end, [[row] for row in order])
            self.assertEqual((found["moves"], found["strict"], found["guard"]), ([], [], []))
            self.assertEqual(found["targets"], {f"page:{row['page']}": row["to"] for row in moves})

    def test_the_guard_s_verdicts(self) -> None:
        for folder in ("Topic", "Topic/live", "Topic/replacement", "Topic/renamed", "Topic/kept", "Topic/kept-out",
                       "Topic/absent/at"):
            (wiki.ROADMAP / folder).mkdir(parents=True, exist_ok=True)
            (wiki.ROADMAP / folder / "README.md").write_text("# Folder\n")
        part = [f"{cards.FRAGMENTS}/2020010{number}T000000Z-part{number}.jsonl" for number in (1, 2, 3)]

        def verdict(one: list[dict], two: list[dict], published: str | None = None) -> list[str]:
            rows = [card_moves.LedgerRow(path, number, row) for path, found in zip(part, (one, two))
                    for number, row in enumerate(found, 1)]
            return card_moves.guard(rows, [path for path in part[:2] if path != published], {published} - {None},
                                    cards.LiveFolders())

        sibling = [self.move("page", 100 + number, f"Topic/live/{number}", f"Topic/replacement/{number}")
                   for number in range(2)]
        cases = [
            ("two moves under a stable folder", sibling[:1], sibling[1:], None, False),
            ("names that only share a prefix", [self.move("folder", 30, "Topic/kept", "Topic/other")],
             [self.move("page", 32, "Topic/kept-out/p", "Topic/live/p")], None, False),
            ("two writers of one missing folder", [self.move("page", 10, "Topic/old/p", "Topic/live/p")],
             [self.retire("statement", 11, "Topic/old/nested/q", 3)], None, True),
            ("a live folder a move goes into", [self.move("page", 10, "Topic/renamed/p", "Topic/live/p")],
             [self.move("folder", 30, "Topic/old", "Topic/renamed")], None, True),
            ("a crossing of a published fragment", [self.retire("statement", 11, "Topic/old/nested/q", 3)],
             [self.move("folder", 30, "Topic/old", "Topic/renamed")], part[1], True),
            ("an append after a published fragment", [self.move("folder", 30, "Topic/old", "Topic/renamed")],
             [self.retire("statement", 11, "Topic/old/nested/q", 3)], part[0], False),
            ("one id at two addresses", [self.move("page", 30, "Topic/live/p", "Topic/replacement/p")],
             [self.retire("statement", 30, "Topic/kept/v", 3)], None, True),
            ("a chain of replacements by id alone", [self.retire("statement", 10, "Topic/live/p", 11)],
             [self.retire("statement", 11, "Topic/replacement/q", 3)], None, False),
        ]
        for name, one, two, published, interacts in cases:
            with self.subTest(name):
                self.assertEqual(bool(verdict(one, two, published)), interacts)
        # A third fragment that moves a folder into the stable stop of two others makes all three pairs interact.
        under = "Topic/absent/at"
        one = card_moves.LedgerRow(part[0], 1, self.move("page", 1, f"{under}/u", "Topic/live/u"))
        two = card_moves.LedgerRow(part[1], 1, self.move("page", 2, f"{under}/v", "Topic/replacement/v"))
        three = card_moves.LedgerRow(part[2], 1, self.move("folder", 3, "Topic/renamed", under))
        self.assertEqual(card_moves.guard([one, two], part[:2], set(), cards.LiveFolders()), [])
        self.assertEqual(len(card_moves.guard([one, two, three], part[:2], {part[2]}, cards.LiveFolders())), 3)


class OccupancyEpochs(unittest.TestCase):
    """The route of an old folder address against a hand-written oracle, when the address had more than one holder: a
    folder that a row moved through it, and folders no article was, which a page's visit made and its leaving
    unmade. A folder row's route for its old address is never replaced by a fallback taken at another time, and a gone
    folder below takes its fallback from what held its parent when it was last used, never from a later or earlier
    holder of that path. Every order of the rows that the checks accept gives the oracle's routes and links."""

    annotations = staticmethod(ChronologyControls.annotations)
    move = staticmethod(ChronologyControls.move)
    retire = staticmethod(ChronologyControls.retire)

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        vault = self.tmp / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(card_moves, "ROOT", self.tmp),
                    patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"),
                    patch.object(cards.sync, "LINKS", vault / "links")):
            one.start()
            self.addCleanup(one.stop)
        self.hook = load_hook()
        self.trees: dict = {}

    def lay_out(self, base: dict, end: dict) -> None:
        shutil.rmtree(wiki.ROADMAP, ignore_errors=True)
        self.base_annotations, self.end_annotations = self.annotations(base), self.annotations(end)
        for page in self.end_annotations:
            page.parent.mkdir(parents=True, exist_ok=True)
            page.write_text("# Page\n")
        self.found = cards.card_folders(self.end_annotations)
        entries = [{"id": name, "kind": "node" if kind == "page" else "scope",
                    "route": f"../roadmap/{name}.html" if kind == "page" else f"../roadmap/{name}/index.html",
                    "title": name} for name, (kind, _) in end.items()]
        entries.append({"id": "roadmap", "kind": "scope", "route": "../roadmap/index.html", "title": "Roadmap"})
        self.pages = self.hook.Pages(self.hook.read_index({"schema": self.hook.INDEX_SCHEMA, "nodes": entries}))
        self.replacements = {af(number): ("page" if kind == "page" else "folder", name)
                             for name, (kind, number) in end.items()}

    @staticmethod
    def files(rows: list[dict]) -> list[tuple[str, bytes]]:
        return [(cards.FROZEN, b""), (f"{cards.FRAGMENTS}/20200101T000000Z-history.jsonl",
                                      "".join(json.dumps(row) + "\n" for row in rows).encode())]

    def checks(self, rows: list[dict]) -> tuple[list[str], list[str], list[str]]:
        """The moves check with the base (the combined ledger against an empty base, as `moves --base` checks it), the
        card check's (with the replay since the base) and the snapshot's. Against the first, the required check's own
        (card_moves.check with its own read of the live folders) gives its errors but those that need the tree."""
        files = self.files(rows)
        base = card_moves.BaseLedger({cards.FROZEN: card_moves.blob_id(b"")}, {cards.FROZEN: b""})
        moves = cards.check_moves(self.end_annotations, self.found, base=base, files=files)
        self.assertEqual(required_check(self.tmp, files, base, self.trees), tree_free(moves))
        return (moves, cards.check_moves(self.end_annotations, self.found, base=base,
                                         base_annotations=self.base_annotations, renames=[], files=files),
                cards.check_moves(self.end_annotations, self.found, files=files))

    def site(self, rows: list[dict]) -> dict:
        """What the hook makes of the rows: the typed routes, every notice's link, refresh and old-anchor elements,
        every old anchor on a live folder page, and the explorer's rewrite table."""
        ledger = self.hook.read_ledger([(path, data.decode()) for path, data in self.files(rows)])
        site = self.hook.Site()
        self.hook.redirects(site, ledger, self.pages, self.replacements, self.tmp / "docs")
        notices = {path: (text.split('<p><a href="', 1)[1].split('"', 1)[0], "http-equiv" in text,
                          RedirectElements.of(text)) for path, text in site.files.items() if path.endswith(".md")}
        anchors = {page: RedirectElements.of("".join(element for _, element in sorted(pairs)))
                   for page, pairs in site.anchors.items()}
        table = (json.loads(site.files[self.hook.SCRIPT].split("var moves = ", 1)[1].split(", own = ")[0])
                 if self.hook.SCRIPT in site.files else {})
        routes = {f"{kind}:{address}": endpoint for (kind, address), endpoint
                  in self.hook.history(ledger, self.pages, self.replacements).items()}
        return {"routes": routes, "notices": notices, "anchors": anchors, "table": table}

    def test_a_folder_s_route_outlives_an_earlier_visit_to_its_address(self) -> None:
        # Folder 2 moves start -> mid -> end; page 3 visits mid/u, a folder no article was, on its way from x to y.
        # Every order of the four rows that the checks accept (each article's own rows in order) gives these routes:
        # mid, which folder 2 left for end, leads to end whenever the page passed through it.
        base = {"T": ("folder", 1), "T/start": ("folder", 2), "T/x": ("page", 3)}
        end = {"T": ("folder", 1), "T/end": ("folder", 2), "T/y": ("page", 3)}
        self.lay_out(base, end)
        rows = [self.move("page", 3, "T/x", "T/mid/u"), self.move("page", 3, "T/mid/u", "T/y"),
                self.move("folder", 2, "T/start", "T/mid"), self.move("folder", 2, "T/mid", "T/end")]
        oracle = {
            "routes": {"folder:T/start": "T/end", "folder:T/mid": "T/end", "page:T/x": "T/y", "page:T/mid/u": "T/y"},
            "notices": {"roadmap/T/start/README.md": ("../end/index.html", True, []),
                        "dependencies/scopes/T/start.md": ("../../../roadmap/T/end/index.html", True, []),
                        "roadmap/T/mid/README.md": ("../end/index.html", False, [("u", "../y.html")]),
                        "dependencies/scopes/T/mid.md": ("../../../roadmap/T/end/index.html", True, []),
                        "roadmap/T/x.md": ("y.html", True, []), "roadmap/T/mid/u.md": ("../y.html", True, [])},
            "anchors": {"roadmap/T/index.html": [("x", "y.html")]},
            "table": {"T/start": "T/end", "T/mid": "T/end", "T/x": "T/y", "T/mid/u": "T/y"}}
        accepted = 0
        for order in itertools.permutations(range(4)):
            ordered = [rows[at] for at in order]
            moves, strict, snapshot = self.checks(ordered)
            lawful = order.index(0) < order.index(1) and order.index(2) < order.index(3)
            with self.subTest(order=order):
                self.assertEqual((not moves, not strict, not snapshot), (lawful, lawful, lawful),
                                 (moves, strict, snapshot))
                if lawful:
                    accepted += 1
                    self.assertEqual(self.site(ordered), oracle)
        self.assertEqual(accepted, 6)

    def test_a_gone_folder_below_takes_its_parent_s_holder_when_it_was_last_used(self) -> None:
        # The same, the page visiting mid/sub/u: sub was in folder 2 when the page left it while folder 2 held mid, and
        # leads to end; it was in a folder no article was when the page left it before folder 2 came or after it left,
        # and leads where T leads, T.
        base = {"T": ("folder", 1), "T/start": ("folder", 2), "T/x": ("page", 3)}
        end = {"T": ("folder", 1), "T/end": ("folder", 2), "T/y": ("page", 3)}
        self.lay_out(base, end)
        rows = [self.move("page", 3, "T/x", "T/mid/sub/u"), self.move("page", 3, "T/mid/sub/u", "T/y"),
                self.move("folder", 2, "T/start", "T/mid"), self.move("folder", 2, "T/mid", "T/end")]
        seen = set()
        for order in itertools.permutations(range(4)):
            if not (order.index(0) < order.index(1) and order.index(2) < order.index(3)):
                continue
            ordered = [rows[at] for at in order]
            self.assertEqual(self.checks(ordered), ([], [], []))
            inside = order.index(2) < order.index(1) < order.index(3)
            sub = "T/end" if inside else "T"
            oracle = {
                "routes": {"folder:T/start": "T/end", "folder:T/mid": "T/end", "folder:T/mid/sub": sub,
                           "page:T/x": "T/y", "page:T/mid/sub/u": "T/y"},
                "notices": {"roadmap/T/start/README.md": ("../end/index.html", True, []),
                            "dependencies/scopes/T/start.md": ("../../../roadmap/T/end/index.html", True, []),
                            "roadmap/T/mid/README.md": ("../end/index.html", True, []),
                            "dependencies/scopes/T/mid.md": ("../../../roadmap/T/end/index.html", True, []),
                            "roadmap/T/mid/sub/README.md": ("../../end/index.html" if inside else "../../index.html",
                                                            False, [("u", "../../y.html")]),
                            "dependencies/scopes/T/mid/sub.md": (
                                f"../../../../roadmap/{'T/end' if inside else 'T'}/index.html", True, []),
                            "roadmap/T/x.md": ("y.html", True, []),
                            "roadmap/T/mid/sub/u.md": ("../../y.html", True, [])},
                "anchors": {"roadmap/T/index.html": [("x", "y.html")]},
                "table": {"T/start": "T/end", "T/mid": "T/end", "T/mid/sub": sub, "T/x": "T/y",
                          "T/mid/sub/u": "T/y"}}
            with self.subTest(order=order):
                self.assertEqual(self.site(ordered), oracle)
            seen.add(inside)
        self.assertEqual(seen, {True, False})

    def test_a_fallback_keeps_the_holder_it_was_bound_to_through_a_card_s_retirement(self) -> None:
        # Folder 41 moves before -> old/r -> after with its page own; page 20 visits old/r/q; page 21 visits
        # old/r/sub/p; the card old (4) is retired for replacement (3). old/r leads to after, as its row says; sub
        # leads to after when the page left it while folder 41 held old/r, else where old/r led then, the card's
        # replacement. Every one of the 22,680 orders that keep each article's rows in order passes the order rule and
        # gives these routes; every 7th of them, and the authored one, gives these notices, anchors and rewrite table,
        # and every 113th passes the full checks, which refuse an order that breaks a chain. (The receipts run every
        # order through all of them.)
        fixed = {"Topic": ("folder", 1), "Topic/live": ("folder", 2), "Topic/replacement": ("card", 3),
                 "Topic/replacement/main": ("page", 7)}
        base = {**fixed, "Topic/old": ("card", 4), "Topic/old/q": ("page", 20), "Topic/before": ("folder", 41),
                "Topic/before/own": ("page", 42), "Topic/live/start": ("page", 21)}
        end = {**fixed, "Topic/live/q": ("page", 20), "Topic/live/p": ("page", 21), "Topic/after": ("folder", 41),
               "Topic/after/own": ("page", 42)}
        self.lay_out(base, end)
        rows = [self.move("page", 20, "Topic/old/q", "Topic/old/r/q"), self.retire("card", 4, "Topic/old", 3),
                self.move("page", 20, "Topic/old/r/q", "Topic/live/q"),
                self.move("folder", 41, "Topic/before", "Topic/old/r"),
                self.move("page", 42, "Topic/before/own", "Topic/old/r/own"),
                self.move("page", 21, "Topic/live/start", "Topic/old/r/sub/p"),
                self.move("page", 21, "Topic/old/r/sub/p", "Topic/live/p"),
                self.move("folder", 41, "Topic/old/r", "Topic/after"),
                self.move("page", 42, "Topic/old/r/own", "Topic/after/own")]
        chains = [(0, 2), (3, 7), (4, 8), (5, 6)]

        def oracle(order: tuple[int, ...]) -> dict:
            inside = order.index(3) < order.index(6) < order.index(7)
            sub = "Topic/after" if inside else "Topic/replacement"
            routes = {"folder:Topic/old": "Topic/replacement", "folder:Topic/old/r": "Topic/after",
                      "folder:Topic/before": "Topic/after", "folder:Topic/old/r/sub": sub,
                      "page:Topic/old/q": "Topic/live/q", "page:Topic/old/r/q": "Topic/live/q",
                      "page:Topic/before/own": "Topic/after/own", "page:Topic/old/r/own": "Topic/after/own",
                      "page:Topic/live/start": "Topic/live/p", "page:Topic/old/r/sub/p": "Topic/live/p"}
            notices = {
                "roadmap/Topic/old/README.md": ("../replacement/index.html", False, [("q", "../live/q.html")]),
                "dependencies/scopes/Topic/old.md": ("../../../roadmap/Topic/replacement/index.html", True, []),
                "roadmap/Topic/old/r/README.md": ("../../after/index.html", False,
                                                  [("own", "../../after/own.html"), ("q", "../../live/q.html")]),
                "dependencies/scopes/Topic/old/r.md": ("../../../../roadmap/Topic/after/index.html", True, []),
                "roadmap/Topic/old/r/sub/README.md": (f"../../../{sub.rsplit('/', 1)[1]}/index.html", False,
                                                      [("p", "../../../live/p.html")]),
                "dependencies/scopes/Topic/old/r/sub.md": (f"../../../../../roadmap/{sub}/index.html", True, []),
                "roadmap/Topic/before/README.md": ("../after/index.html", False, [("own", "../after/own.html")]),
                "dependencies/scopes/Topic/before.md": ("../../../roadmap/Topic/after/index.html", True, []),
                "roadmap/Topic/old/q.md": ("../live/q.html", True, []),
                "roadmap/Topic/old/r/q.md": ("../../live/q.html", True, []),
                "roadmap/Topic/before/own.md": ("../after/own.html", True, []),
                "roadmap/Topic/old/r/own.md": ("../../after/own.html", True, []),
                "roadmap/Topic/live/start.md": ("p.html", True, []),
                "roadmap/Topic/old/r/sub/p.md": ("../../../live/p.html", True, [])}
            return {"routes": routes, "notices": notices, "anchors": {"roadmap/Topic/live/index.html": [
                ("start", "p.html")]}, "table": {key.split(":", 1)[1]: value for key, value in routes.items()}}

        orders = [order for order in itertools.permutations(range(9))
                  if all(order.index(one) < order.index(two) for one, two in chains)]
        self.assertEqual(len(orders), 22680)
        inside = 0
        for number, order in enumerate(orders):
            ordered = [rows[at] for at in order]
            lines = [card_moves.LedgerRow(cards.FRAGMENTS + "/x.jsonl", line, row)
                     for line, row in enumerate(ordered, 1)]
            self.assertEqual(card_moves.order_problems(lines, None), [], order)
            expected = oracle(order)
            if number % 7 == 0 or order == tuple(range(9)):
                self.assertEqual(self.site(ordered), expected, order)
            else:
                ledger = self.hook.read_ledger([(path, data.decode()) for path, data in self.files(ordered)])
                self.assertEqual({f"{kind}:{address}": endpoint for (kind, address), endpoint
                                  in self.hook.history(ledger, self.pages, self.replacements).items()},
                                 expected["routes"], order)
            inside += order.index(3) < order.index(6) < order.index(7)
            if number % 113 == 0 or order == tuple(range(9)):
                self.assertEqual(self.checks(ordered), ([], [], []), order)
        self.assertTrue(0 < inside < len(orders))
        broken = [rows[at] for at in (2, 0, 1, 3, 4, 5, 6, 7, 8)]
        moves, strict, snapshot = self.checks(broken)
        self.assertTrue(moves and strict and snapshot)


    def shared(self, children: list[tuple[str, int, str, str]]) -> tuple[list[dict], dict, dict]:
        """Folder 2 moving T/start -> T/mid -> T/end, and pages each visiting one gone folder below T/mid once: for each
        child (its path below T/mid, the page's id, its address before and after), the page's two rows. The rows (the
        folder's first), the base and the end."""
        base = {"T": ("folder", 1), "T/start": ("folder", 2)}
        end = {"T": ("folder", 1), "T/end": ("folder", 2)}
        rows = [self.move("folder", 2, "T/start", "T/mid"), self.move("folder", 2, "T/mid", "T/end")]
        for child, number, before, after in children:
            base[f"T/{before}"] = end[f"T/{after}"] = ("page", number)
            leaf = f"T/mid/{child}/p{number}"
            rows += [self.move("page", number, f"T/{before}", leaf), self.move("page", number, leaf, f"T/{after}")]
        return rows, base, end

    def shared_oracle(self, children: list[tuple[str, int, str, str]], order: tuple[int, ...]) -> dict:
        """What the history ``order`` of shared()'s rows says: each gone folder leads to T/end when its page left it
        while folder 2 held T/mid, else where T leads, T; a gone folder holding several of them leads where it led when
        it was first left; T/mid and T/start lead to T/end, as the folder rows say."""
        def held(row: int) -> bool:
            return order.index(0) < order.index(row) < order.index(1)

        def name(endpoint: str) -> str:
            return endpoint.rsplit("/", 1)[1] if endpoint != "T" else ""

        routes = {"folder:T/start": "T/end", "folder:T/mid": "T/end"}
        notices = {"roadmap/T/start/README.md": ("../end/index.html", True, []),
                   "dependencies/scopes/T/start.md": ("../../../roadmap/T/end/index.html", True, []),
                   "roadmap/T/mid/README.md": ("../end/index.html", True, []),
                   "dependencies/scopes/T/mid.md": ("../../../roadmap/T/end/index.html", True, [])}
        anchors, first = [], {}
        for at, (child, number, before, after) in enumerate(children):
            leave = 3 + 2 * at
            endpoint = "T/end" if held(leave) else "T"
            parts = child.split("/")
            leaf = f"T/mid/{child}/p{number}"
            up = "../" * (len(parts) + 1)
            routes[f"folder:T/mid/{child}"] = endpoint
            routes[f"page:T/{before}"] = routes[f"page:{leaf}"] = f"T/{after}"
            notices[f"roadmap/T/mid/{child}/README.md"] = (f"{up}{name(endpoint) + '/' if name(endpoint) else ''}"
                                                           "index.html", False, [(f"p{number}", f"{up}{after}.html")])
            notices[f"dependencies/scopes/T/mid/{child}.md"] = (
                f"{'../' * (len(parts) + 3)}roadmap/{endpoint}/index.html", True, [])
            notices[f"roadmap/T/{before}.md"] = (f"{after}.html", True, [])
            notices[f"roadmap/{leaf}.md"] = (f"{up}{after}.html", True, [])
            anchors.append((before, f"{after}.html"))
            # The gone folders between T/mid and the child, each first left when its first page left.
            for depth in range(1, len(parts)):
                between = "/".join(parts[:depth])
                if between not in first or order.index(leave) < order.index(first[between]):
                    first[between] = leave
        for between, leave in first.items():
            endpoint = "T/end" if held(leave) else "T"
            up = "../" * (between.count("/") + 2)
            routes[f"folder:T/mid/{between}"] = endpoint
            notices[f"roadmap/T/mid/{between}/README.md"] = (
                f"{up}{name(endpoint) + '/' if name(endpoint) else ''}index.html", True, [])
            notices[f"dependencies/scopes/T/mid/{between}.md"] = (
                f"{'../' * (between.count('/') + 4)}roadmap/{endpoint}/index.html", True, [])
        return {"routes": routes, "notices": notices, "anchors": {"roadmap/T/index.html": sorted(anchors)},
                "table": {key.split(":", 1)[1]: value for key, value in routes.items()}}

    def every_shared_order(self, children: list[tuple[str, int, str, str]], sites: int = 1, checks: int = 1) -> dict:
        """Every order of shared()'s rows that keeps each article's rows in order, against shared_oracle: the routes of
        each; the notices, anchors and rewrite table of every ``sites``-th; the required step's, the card check's and
        the snapshot's verdicts on every ``checks``-th. The site of each order, by order, for those compared."""
        rows, base, end = self.shared(children)
        self.lay_out(base, end)
        chains = [(0, 1)] + [(2 + 2 * at, 3 + 2 * at) for at in range(len(children))]
        orders = [order for order in itertools.permutations(range(len(rows)))
                  if all(order.index(one) < order.index(two) for one, two in chains)]
        seen = {}
        for number, order in enumerate(orders):
            ordered = [rows[at] for at in order]
            expected = self.shared_oracle(children, order)
            if number % sites == 0:
                seen[order] = self.site(ordered)
                self.assertEqual(seen[order], expected, order)
            else:
                ledger = self.hook.read_ledger([(path, data.decode()) for path, data in self.files(ordered)])
                self.assertEqual({f"{kind}:{address}": endpoint for (kind, address), endpoint
                                  in self.hook.history(ledger, self.pages, self.replacements).items()},
                                 expected["routes"], order)
            if number % checks == 0:
                self.assertEqual(self.checks(ordered), ([], [], []), order)
        return seen

    def test_gone_folders_below_one_gone_folder_take_each_their_own_holder(self) -> None:
        # Page 3 visits mid/sub/early and page 4 mid/sub/late, each once, the gone folder sub between them; folder 2
        # moves start -> mid -> end. In each of the 90 orders that keep each article's rows in order, which pass every
        # check, a child leads to T/end when its page left it while folder 2 held mid, else to T, whatever the other
        # child did. Among them, as recorded with their links: the six rows as authored (early before folder 2 came,
        # late while it was there), the mirror (early while it was there, late after it left), both before, both while.
        children = [("sub/early", 3, "x", "x2"), ("sub/late", 4, "y", "y2")]
        seen = self.every_shared_order(children)
        self.assertEqual(len(seen), 90)
        early, late = "roadmap/T/mid/sub/early/README.md", "roadmap/T/mid/sub/late/README.md"
        for order, hrefs in (((2, 3, 0, 4, 5, 1), ("../../../index.html", "../../../end/index.html")),
                             ((0, 2, 3, 1, 4, 5), ("../../../end/index.html", "../../../index.html")),
                             ((2, 3, 4, 5, 0, 1), ("../../../index.html", "../../../index.html")),
                             ((0, 2, 3, 4, 5, 1), ("../../../end/index.html", "../../../end/index.html"))):
            self.assertEqual((seen[order]["notices"][early][0], seen[order]["notices"][late][0]), hrefs, order)

    def test_gone_folders_visited_before_during_and_after_a_folder_s_stay(self) -> None:
        # Three pages, each visiting its own folder below the gone mid/sub once, and folder 2's stay at mid: in each
        # of the 2,520 orders that keep each article's rows in order, each child leads to T/end exactly when its page
        # left it while folder 2 held mid. Every 5th order is compared on notices, anchors and the rewrite table too,
        # and every 50th passes the full checks.
        children = [("sub/one", 3, "x", "x2"), ("sub/two", 4, "y", "y2"), ("sub/three", 5, "z", "z2")]
        seen = self.every_shared_order(children, sites=5, checks=50)
        self.assertEqual(len(seen), 504)
        # Before, during and after, in one order: one before folder 2 came, two while it was there, three after it left.
        found = self.site([self.shared(children)[0][at] for at in (2, 3, 0, 4, 5, 1, 6, 7)])
        self.assertEqual([found["routes"][f"folder:T/mid/sub/{child}"] for child in ("one", "two", "three")],
                         ["T", "T/end", "T"])

    def test_gone_folders_below_two_gone_folders_are_apart(self) -> None:
        # The same two pages, one through mid/sub/early and one through mid/apart/late: no gone folder between them is
        # shared, and each leads where its own page's time says, in each of the 90 orders.
        self.assertEqual(len(self.every_shared_order([("sub/early", 3, "x", "x2"), ("apart/late", 4, "y", "y2")])), 90)


class RedirectElements:
    """The old-anchor elements of a notice, as (anchor, link) pairs."""

    @staticmethod
    def of(text: str) -> list[tuple[str, str]]:
        return re.findall(r'<p class="atlas-moved" id="([^"]+)">This statement moved: <a href="([^"]+)">', text)


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

    FRAGMENT = "scripts/card-moves.d/20200101T000000Z-change.jsonl"

    def change(self, base: str, *rows: dict) -> list[str]:
        """Commit the change with the ledger ``rows``, in a fragment of its own, and check it as the card job checks a
        pull request on ``base``, with the base's ledger extracted as the job extracts it: its errors."""
        fragment = wiki.ROOT / self.FRAGMENT
        fragment.parent.mkdir(exist_ok=True)
        fragment.write_text("".join(json.dumps(row) + "\n" for row in rows))
        head = self.commit("change")
        work = Path(tempfile.mkdtemp(dir=self.scratch))
        renames = work / "renames.tsv"
        renames.write_text(self.git("-c", "diff.renameLimit=0", "diff", "--name-status", "-M", base, head, "--",
                                    "blueprint/roadmap"))
        (work / "links").mkdir()
        (work / "links" / "Algebra.jsonl").write_text(self.git("show", f"{base}:blueprint/links/Algebra.jsonl"))
        (work / "scripts").mkdir()
        (work / "scripts" / cards.MOVES).write_text(self.git("show", f"{base}:scripts/{cards.MOVES}"))
        if self.git("ls-tree", base, "--", cards.FRAGMENTS):
            archive = subprocess.run(["git", "-C", str(self.tmp), "archive", base, cards.FRAGMENTS], check=True,
                                     capture_output=True).stdout
            subprocess.run(["tar", "-x", "-C", str(work)], input=archive, check=True)
        known, problems = card_moves.base_from_folder(work / "scripts")
        self.assertEqual(problems, [])
        return cards.check(dependencies=self.extraction(), base_ledger=known,
                           base_annotations=cards.read_links(work / "links"), renames=cards.read_renames(renames))[0]

    def site(self, base: str, *rows: dict):
        """The change with its rows, which the strict check accepts, then the site's redirects."""
        self.assertEqual(self.change(base, *rows), [])
        ledger = [("scripts/card-moves.jsonl", ""), (self.FRAGMENT, "".join(json.dumps(row) + "\n" for row in rows))]
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
