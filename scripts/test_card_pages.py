"""The site's cards (docs/cards.md#reading): hooks/card_pages.py shows card data only from a rollup of the commit being
built, shows each card's derived edges with their witnesses, and keeps every address the move ledger retired, with the
ledger check's receipt and with or without card data."""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import logging
import os
import posixpath
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from collections import Counter
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def load_hook():
    """Import hooks/card_pages.py, which MkDocs loads by path rather than as a package module."""
    spec = importlib.util.spec_from_file_location("atlas_hook_card_pages", ROOT / "hooks" / "card_pages.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


card_pages = load_hook()
COMMIT = "c7df2d47c165e81f305e67eb4263db54d516aae9"


def af(number: int) -> str:
    return f"af_{number:024x}"


def leaf(node_id: str, title: str | None = None, own_page: bool = False, **extra) -> dict:
    """An index entry of a statement page: boxed on its folder's page, or published as a page of its own."""
    folder, name = node_id.rsplit("/", 1)
    route = f"../roadmap/{node_id}.html" if own_page else f"../roadmap/{folder}/index.html#{name}"
    return {"id": node_id, "kind": "node", "route": route, "title": title or name, "scope": folder,
            "status": "fully_proved", "result": True, **extra}


def folder(node_id: str, title: str | None = None) -> dict:
    route = "../roadmap/index.html" if node_id == "roadmap" else f"../roadmap/{node_id}/index.html"
    return {"id": node_id, "kind": "scope", "route": route, "title": title or node_id.rsplit("/", 1)[-1],
            "scope": node_id, "status": "fully_proved", "result": False}


def index(*entries: dict) -> dict:
    """Render's search index of the given pages, with the folders above them."""
    nodes = {entry["id"]: entry for entry in entries}
    for entry in entries:
        above = entry["id"]
        while "/" in above:
            above = above.rsplit("/", 1)[0]
            nodes.setdefault(above, folder(above))
    nodes.setdefault("roadmap", folder("roadmap", "ATLAS roadmap"))
    return {"schema": "autoform-dag-search/v1", "nodes": list(nodes.values()), "relations": []}


def flags(status: str) -> dict:
    """A statement's row in the rollup's `pages` table that gives it ``status``."""
    marker = status in ("stale", "held", "not_ready", "page_only")
    return {"credit": "none" if marker else "mathlib" if status == "mathlib" else "atlas", "held": status == "held",
            "not_ready": status == "not_ready", "stale": status == "stale",
            "state": "can_state" if marker else status, "kind": None if marker else "theorem"}


def card(number: int, folder_id: str, pages: list[str], main: str | None = None, headline: str = "fully_proved",
         kind: str = "result", supports: tuple[str, ...] = (), **buckets: int) -> dict:
    """A card of the rollup: its main statement has the status ``headline``, its other statements the statuses
    ``buckets`` counts (all fully proved by default), in the order of their paths."""
    members = [f"{folder_id}/{page}" for page in pages]
    main = main or members[0]
    supporting = {key: 0 for key in card_pages.LABELS}
    supporting.update(buckets or {"fully_proved": len(members) - 1})
    status = {"page": main, "article_id": af(100 + number), "headline": headline}
    status.update({key: value for key, value in flags(headline).items() if key != "kind"})
    return {"id": af(number), "folder": folder_id, "title": folder_id, "kind": kind, "importance": "key",
            "level": "graduate", "main": status, "pages": sorted(members), "supports": list(supports), "seeds": [],
            "supporting": {"total": len(members) - 1, **supporting}}


def step(source: str, target: str, kind: str = "statement", origin: str = "compiled") -> dict:
    return {"source": source, "target": target, "kind": kind, "origin": origin}


def uses(source: dict, target: dict, *witnesses: dict) -> dict:
    return {"from": source["id"], "to": target["id"], "witnesses": list(witnesses),
            "statement": sum(w["kind"] == "statement" for w in witnesses),
            "proof": sum(w["kind"] == "proof" for w in witnesses),
            "origins": dict(sorted(Counter(w["origin"] for w in witnesses).items()))}


def rollup(cards: list[dict], uses_edges=(), needs_edges=(), clusters=(), commit: str = COMMIT) -> dict:
    """A rollup as scripts/cards.py writes it: its `pages` table, counts and accounting agree with its cards."""
    table = {}
    for one in cards:
        others = [page for page in one["pages"] if page != one["main"]["page"]]
        statuses = [key for key in card_pages.LABELS for _ in range(one["supporting"][key])]
        for page, status in [(one["main"]["page"], one["main"]["headline"]), *zip(others, statuses)]:
            table[page] = {**flags(status), "article_id": None, "card": one["id"]}
    for edge in [*uses_edges, *needs_edges]:
        for walk in (edge.get("witnesses"), edge.get("statement_walk"), edge.get("walk")):
            for one in walk or []:
                for page in (one["source"], one["target"]):
                    table.setdefault(page, {**flags("fully_proved"), "article_id": None, "card": None})
    for one in cards:
        for page in one["supports"]:
            table.setdefault(page, {**flags("fully_proved"), "article_id": None, "card": None})
    witnesses = sum(len(edge["witnesses"]) for edge in uses_edges)
    return {"schema": "atlas-cards/v1", "commit": commit, "cards": cards, "pages": table, "uses": list(uses_edges),
            "needs": list(needs_edges), "clusters": list(clusters), "unassigned": [],
            "edges": {"card_to_card": witnesses, "total": witnesses} if witnesses else {},
            "counts": {"cards": len(cards), "pages": sum(len(one["pages"]) for one in cards),
                       "uses": len(uses_edges), "needs": len(needs_edges), "clusters": len(clusters),
                       "unassigned": 0}}


def ledger(*rows: dict) -> str:
    return "".join(json.dumps(row) + "\n" for row in rows)


def rename(old: str, new: str, number: int, pages: dict[str, int] | None = None,
           folders: dict[str, int] | None = None) -> list[dict]:
    """The rows of renaming the folder ``old`` to ``new``: the folder's own row and one for each page and each
    folder inside it, by name with its article number, since a folder row moves the folder alone
    (docs/cards.md#move-ledger). A folder inside it moves alone too: what it holds needs rows of its own."""
    rows = [{"folder": old, "to": new, "article_id": af(number)}]
    rows += [{"page": f"{old}/{name}", "to": f"{new}/{name}", "article_id": af(page)}
             for name, page in (pages or {}).items()]
    rows += [{"folder": f"{old}/{name}", "to": f"{new}/{name}", "article_id": af(folder)}
             for name, folder in (folders or {}).items()]
    return rows


def links_digest(files: dict[str, bytes | None]) -> str:
    """The digest of a links folder's files, by name, as docs/cards.md#move-ledger gives it: sha256 over each file,
    in sorted order of name, as its name, a NUL, its length in bytes (`-` for a defaults file that is no regular
    file), a NUL and its bytes."""
    digest = hashlib.sha256()
    for name in sorted(files):
        data = files[name]
        size = b"-" if data is None else str(len(data)).encode()
        digest.update(name.encode() + b"\0" + size + b"\0" + (data or b""))
    return digest.hexdigest()


def ledger_digest(files: list[tuple[str, bytes]]) -> str:
    """The digest of the move ledger's files, by path in logical order, as docs/cards.md#reading gives it: sha256 over
    each file, as its path in the repository, a NUL, its length in bytes in decimal, a NUL and its bytes."""
    digest = hashlib.sha256()
    for path, data in files:
        digest.update(path.encode() + b"\0" + str(len(data)).encode() + b"\0" + data)
    return digest.hexdigest()


def receipt(commit: str, rows: str | list[tuple[str, bytes]], cards: dict[str, str],
            links: dict[str, bytes | None] | None = None, complete: bool = True,
            replacements: dict[str, dict[str, str]] | None = None) -> dict:
    """The receipt `scripts/cards.py moves` writes for the commit, the ledger (the frozen file's ``rows``, or each
    file's path and bytes in logical order), the links folder's files, the cards it lists and the replacements of the
    ledger's retirements (by default, every listed card, as a folder)."""
    if replacements is None:
        replacements = {card: {"kind": "folder", "node": folder} for card, folder in cards.items()}
    files = [("scripts/card-moves.jsonl", rows.encode())] if isinstance(rows, str) else rows
    return {"schema": "atlas-card-moves/v3", "commit": commit, "ledger_sha256": ledger_digest(files),
            "annotations_sha256": links_digest(links or {}), "cards": cards, "cards_complete": complete,
            "replacements": replacements}


T = "A/f/t"


class Library:
    """Two cards that use one another, X and Y in one topic, and Z in another, whose main statement needs X's
    through a statement page in no card."""

    entries = [
        leaf(f"{T}/x/x-main", "Main of X"), leaf(f"{T}/x/x-lemma", "Lemma of X"),
        leaf(f"{T}/y/y-main", "Main of Y"), leaf(f"{T}/y/y-left", "Left of Y"),
        leaf("A/f/u/z/z-main", "Main of Z"), leaf("A/f/u/helper", "A helper"),
        folder(f"{T}/x", "Card X"), folder(f"{T}/y", "Card Y"), folder("A/f/u/z", "Card Z"),
    ]

    def __init__(self):
        x = card(1, f"{T}/x", ["x-main", "x-lemma"], main=f"{T}/x/x-main")
        y = card(2, f"{T}/y", ["y-main", "y-left"], main=f"{T}/y/y-main", kind="concept")
        z = card(3, "A/f/u/z", ["z-main"], headline="page_only", supports=("A/f/u/helper",))
        self.x, self.y, self.z = x, y, z
        self.data = rollup(
            [x, y, z],
            [uses(x, y, step(f"{T}/x/x-lemma", f"{T}/y/y-left", "proof", "planned"),
                  step(f"{T}/x/x-main", f"{T}/y/y-main")),
             uses(y, x, step(f"{T}/y/y-left", f"{T}/x/x-lemma", "proof"))],
            [{"from": x["id"], "to": y["id"], "phase": "statement",
              "statement_walk": [step(f"{T}/x/x-main", f"{T}/y/y-main")]},
             {"from": z["id"], "to": x["id"], "phase": "proof",
              "walk": [step("A/f/u/z/z-main", "A/f/u/helper", "proof"), step("A/f/u/helper", f"{T}/x/x-main")]}],
            [{"cards": [x["id"], y["id"]], "edges": [[x["id"], y["id"]], [y["id"], x["id"]]],
              "example_cycle": [x["id"], y["id"], x["id"]]}])

    def build(self, data: dict | None = None, rows: str = "") -> card_pages.Site:
        with tempfile.TemporaryDirectory() as docs:
            return card_pages.build(self.data if data is None else data, index(*self.entries), rows, Path(docs))


class CardBlockTests(unittest.TestCase):
    def setUp(self) -> None:
        self.library = Library()
        self.site = self.library.build()

    def block(self, folder_id: str) -> str:
        return self.site.blocks[f"roadmap/{folder_id}/index.html"]

    def test_each_card_page_gets_one_block(self) -> None:
        self.assertEqual(sorted(self.site.blocks), [f"roadmap/A/f/t/{name}/index.html" for name in ("x", "y")]
                         + ["roadmap/A/f/u/z/index.html"])

    def test_the_block_shows_the_card_its_main_statement_and_its_progress(self) -> None:
        block = self.block(f"{T}/x")
        self.assertIn("<strong>Result card</strong> · importance: key · level: graduate", block)
        self.assertIn('Main statement: <a href="#x-main">Main of X</a>: <span class="atlas-card-state '
                      'atlas-card-fully_proved">fully proved</span>', block)
        self.assertIn("<p>1 supporting statement: 1 fully proved</p>", block)
        self.assertIn("<strong>Concept card</strong>", self.block(f"{T}/y"))
        # A page-only main statement is never shown as ready; a card without other statements says so, and the pages
        # it presents from elsewhere are listed apart.
        z = self.block("A/f/u/z")
        self.assertIn('<span class="atlas-card-state atlas-card-page_only">page only</span>', z)
        self.assertIn("<p>No supporting statement.</p>", z)
        self.assertIn('<p>Also presents: <a href="../helper.html">A helper</a></p>', z.replace(
            "../index.html#helper", "../helper.html"))

    def test_uses_both_ways_names_each_typed_witness(self) -> None:
        block = self.block(f"{T}/x")
        self.assertIn('<dt>Uses</dt><dd><details><summary><a href="../y/index.html">Card Y</a> · 1 statement use, '
                      '1 proof use</summary><ul><li><a href="#x-lemma">Lemma of X</a> uses '
                      '<a href="../y/index.html#y-left">Left of Y</a> in its proof <span class="atlas-card-origin" '
                      'title="A prerequisite a planned page names">planned</span></li><li><a href="#x-main">Main of '
                      'X</a> uses <a href="../y/index.html#y-main">Main of Y</a> in its statement</li></ul></details>'
                      "</dd>", block)
        self.assertIn('<dt>Used by</dt><dd><details><summary><a href="../y/index.html">Card Y</a> · 1 proof use'
                      '</summary><ul><li><a href="../y/index.html#y-left">Left of Y</a> uses <a href="#x-lemma">Lemma '
                      "of X</a> in its proof</li></ul></details></dd>", block)

    def test_needs_both_ways_shows_its_walk(self) -> None:
        self.assertIn('<dt>Needs</dt><dd><details><summary><a href="../y/index.html">Card Y</a> · through statements'
                      '</summary><ol><li><a href="#x-main">Main of X</a> uses <a href="../y/index.html#y-main">Main of '
                      "Y</a> in its statement</li></ol></details></dd>", self.block(f"{T}/x"))
        needed = ('<dt>Needed by</dt><dd><details><summary><a href="../../u/z/index.html">Card Z</a> · through a '
                  'proof</summary><ol><li><a href="../../u/z/index.html#z-main">Main of Z</a> uses '
                  '<a href="../../u/index.html#helper">A helper</a> in its proof</li><li><a '
                  'href="../../u/index.html#helper">A helper</a> uses <a href="#x-main">Main of X</a> in its '
                  "statement</li></ol></details></dd>")
        self.assertIn(needed, self.block(f"{T}/x"))
        self.assertIn('<dt>Needs</dt><dd><details><summary><a href="../../t/x/index.html">Card X</a> · through a proof',
                      self.block("A/f/u/z"))

    def test_a_card_in_a_cycle_shows_its_members_and_an_example_cycle_with_its_witnesses(self) -> None:
        block = self.block(f"{T}/y")
        self.assertIn('<dt>In a mutually reachable group of 2 cards</dt><dd><p>Each of these cards uses every other '
                      'one, directly or through cards of the group: <a href="../x/index.html">Card X</a>, <a '
                      'href="index.html">Card Y</a>. One cycle among them: <a href="../x/index.html">Card X</a> → <a '
                      'href="index.html">Card Y</a> → <a href="../x/index.html">Card X</a>.</p>', block)
        self.assertIn('<li><a href="index.html">Card Y</a> uses <a href="../x/index.html">Card X</a>:<ul><li><a '
                      'href="#y-left">Left of Y</a> uses <a href="../x/index.html#x-lemma">Lemma of X</a> in its proof'
                      "</li></ul></li>", block)
        self.assertNotIn("mutually reachable", self.block("A/f/u/z"))

    def test_a_group_with_no_cycle_through_all_its_cards_is_not_called_a_cycle(self) -> None:
        # A uses B and C, and each uses A: the three cards reach one another, but no cycle passes through all three.
        a, b, c = (card(number, f"{T}/{name}", [f"{name}1"]) for number, name in ((1, "a"), (2, "b"), (3, "c")))
        edges = [uses(a, b, step(f"{T}/a/a1", f"{T}/b/b1")), uses(a, c, step(f"{T}/a/a1", f"{T}/c/c1")),
                 uses(b, a, step(f"{T}/b/b1", f"{T}/a/a1", "proof")),
                 uses(c, a, step(f"{T}/c/c1", f"{T}/a/a1", "proof"))]
        group = {"cards": [a["id"], b["id"], c["id"]], "example_cycle": [a["id"], b["id"], a["id"]],
                 "edges": sorted([edge["from"], edge["to"]] for edge in edges)}
        entries = [leaf(f"{T}/{name}/{name}1") for name in "abc"] + [folder(f"{T}/{name}", f"Card {name.upper()}")
                                                                    for name in "abc"]
        with tempfile.TemporaryDirectory() as docs:
            site = card_pages.build(rollup([a, b, c], edges, (), [group]), index(*entries), "", Path(docs))
        block = site.blocks[f"roadmap/{T}/c/index.html"]
        self.assertIn("<dt>In a mutually reachable group of 3 cards</dt>", block)
        self.assertIn('One cycle among them: <a href="../a/index.html">Card A</a> → <a href="../b/index.html">Card B'
                      '</a> → <a href="../a/index.html">Card A</a>.', block)
        self.assertNotIn("cycle of", block)
        self.assertNotIn("circle", block)

    def test_a_card_with_no_edge_says_so(self) -> None:
        lone = card(1, f"{T}/x", ["x-main", "x-lemma"], main=f"{T}/x/x-main")
        block = self.library.build(rollup([lone])).blocks[f"roadmap/{T}/x/index.html"]
        self.assertIn("<p>No other card uses this one, and this one uses no other card.</p>", block)
        self.assertNotIn("<dl", block)

    def test_titles_read_as_the_site_shows_them(self) -> None:
        parts = {"format": "inline-parts-v1", "source": "x", "parts": [["text", "Bound <a & b> for "],
                                                                      ["math", "\\(L^3\\)"], ["code", "f.x"]]}
        self.assertEqual(card_pages.title_html({"title": "x", "reading_title": parts}),
                         'Bound &lt;a &amp; b&gt; for <span class="arithmatex">\\(L^3\\)</span><code>f.x</code>')
        self.assertEqual(card_pages.title_html({"title": "The order `<₀` on ``a`b`` worms"}),
                         "The order <code>&lt;₀</code> on <code>a`b</code> worms")
        self.assertEqual(card_pages.code_spans("an `unclosed span"), "an `unclosed span")
        with self.assertRaises(card_pages.CardDataError):
            card_pages.title_html({"title": "x", "reading_title": {"format": "inline-parts-v1",
                                                                   "parts": [["html", "<b>"]]}})


class CardDataTests(unittest.TestCase):
    """The site shows card data only when every part of it is well formed and names what the site publishes."""

    def setUp(self) -> None:
        self.library = Library()

    def assertRejected(self, data: dict) -> None:
        with self.assertRaises(card_pages.CardDataError):
            self.library.build(data)

    def test_well_formed_data_passes(self) -> None:
        self.assertEqual(self.library.build().cards, 3)

    def test_malformed_or_inconsistent_data_is_rejected(self) -> None:
        def changed(change) -> dict:
            data = json.loads(json.dumps(self.library.data))
            change(data)
            return data

        for name, change in {
            "schema": lambda d: d.update(schema="atlas-cards/v2"),
            "unknown headline": lambda d: d["cards"][0]["main"].update(headline="ready"),
            "main outside the card": lambda d: d["cards"][0]["main"].update(page=f"{T}/y/y-main"),
            "unpublished folder": lambda d: d["cards"][0].update(folder=f"{T}/gone"),
            "unpublished statement": lambda d: d["cards"][0]["pages"].append(f"{T}/x/gone"),
            "progress that does not add up": lambda d: d["cards"][0]["supporting"].update(fully_proved=5),
            "witness of another card": lambda d: d["uses"][0]["witnesses"][0].update(source="A/f/u/z/z-main"),
            "unknown origin": lambda d: d["uses"][0]["witnesses"][0].update(origin="guessed"),
            "counts that are not the witnesses'": lambda d: d["uses"][0].update(statement=3),
            "broken walk": lambda d: d["needs"][1]["walk"].pop(0),
            "proof step in a statement walk": lambda d: d["needs"][0]["statement_walk"][0].update(kind="proof"),
            "proof walk without a proof step": lambda d: d["needs"][1]["walk"][0].update(kind="statement"),
            "open example cycle": lambda d: d["clusters"][0]["example_cycle"].pop(),
            "card listed twice": lambda d: d["cards"].append(d["cards"][0]),
            "edge listed twice": lambda d: (d["uses"].append(d["uses"][0]), d["counts"].update(uses=3)),
            # Parts that restate others and disagree with them.
            "relations cleared, counts kept": lambda d: d.update(uses=[], needs=[], clusters=[]),
            "a page-only main shown as fully proved": lambda d: d["cards"][2]["main"].update(headline="fully_proved"),
            "a main's markers not its row's": lambda d: d["cards"][0]["main"].update(held=True),
            "progress not its statements' rows": lambda d: d["cards"][0]["supporting"].update(fully_proved=0,
                                                                                               can_prove=1),
            "a row naming another card": lambda d: d["pages"][f"{T}/x/x-lemma"].update(card=af(2)),
            "a row of no card naming one": lambda d: d["pages"]["A/f/u/helper"].update(card=af(3)),
            "origins not the witnesses'": lambda d: d["uses"][0]["origins"].update(compiled=5),
            "accounting not the witnesses'": lambda d: d["edges"].update(card_to_card=2, total=2),
            "a cluster dropped": lambda d: (d["clusters"].clear(), d["counts"].update(clusters=0)),
            "a cluster's edges not its uses": lambda d: d["clusters"][0]["edges"].pop(),
            "a walk through another card's main": lambda d: (d["needs"][1]["walk"][0].update(target=f"{T}/y/y-main"),
                                                            d["needs"][1]["walk"][1].update(source=f"{T}/y/y-main")),
            "card in two clusters": lambda d: d["clusters"].append(d["clusters"][0]),
        }.items():
            with self.subTest(name):
                self.assertRejected(changed(change))

    def test_a_walk_is_worded_by_its_steps(self) -> None:
        statement, proof = step("A/x", "A/y"), step("A/y", "A/z", "proof")
        self.assertEqual(card_pages.walk_phrase([statement, statement]), "through statements")
        self.assertEqual(card_pages.walk_phrase([statement, proof]), "through a proof")

    def test_a_held_main_is_shown_held(self) -> None:
        held = card(1, f"{T}/x", ["x-main", "x-lemma"], main=f"{T}/x/x-main", headline="held")
        block = self.library.build(rollup([held])).blocks[f"roadmap/{T}/x/index.html"]
        self.assertIn('<span class="atlas-card-state atlas-card-held">held</span>', block)
        changed = rollup([held])
        changed["cards"][0]["main"]["headline"] = "fully_proved"
        self.assertRejected(changed)

    def test_a_planned_main_with_a_kind_is_shown_by_its_state(self) -> None:
        # A planned page with the kind lean-facts gives one that counts as a statement not yet in Lean shows
        # Autoform's state, as its task does; with no kind it is page only.
        typed = card(1, f"{T}/x", ["x-main", "x-lemma"], main=f"{T}/x/x-main", headline="can_state")
        data = rollup([typed])
        data["cards"][0]["main"]["credit"] = "none"
        data["pages"][f"{T}/x/x-main"].update(credit="none", kind="def")
        block = self.library.build(data).blocks[f"roadmap/{T}/x/index.html"]
        self.assertIn('<span class="atlas-card-state atlas-card-can_state">ready to state</span>', block)
        data["pages"][f"{T}/x/x-main"]["kind"] = None
        self.assertRejected(data)

    def test_a_route_outside_the_site_is_rejected(self) -> None:
        for route in ("../../outside.html", "/roadmap/A/index.html", "https://example.com/a.html",
                      "../roadmap/A/index"):
            with self.subTest(route), self.assertRaises(card_pages.CardDataError):
                card_pages.read_index(index({"id": "A/x", "kind": "node", "route": route, "title": "x"}))

    def test_the_bridge_and_mathlib_origins_a_registry_will_add_are_shown(self) -> None:
        data = json.loads(json.dumps(self.library.data))
        data["uses"][1]["witnesses"][0]["origin"] = "bridge"
        data["uses"][1]["origins"] = {"bridge": 1}
        self.assertIn('title="From an ATLAS declaration to a Mathlib one">bridge</span>',
                      self.library.build(data).blocks[f"roadmap/{T}/x/index.html"])


class RedirectTests(unittest.TestCase):
    """Every old address of the move ledger keeps leading to its page (docs/cards.md#reading), for the route
    shapes render publishes: a statement with a declaration kind boxed on its folder's page, any other statement
    on its own page, a folder on its page, and explorer links `#node=<address>`."""

    def site(self, entries: list[dict], cards: list[dict], *rows: dict) -> card_pages.Site:
        with tempfile.TemporaryDirectory() as docs:
            return card_pages.build(rollup(cards), index(*entries), ledger(*rows), Path(docs))

    @staticmethod
    def moves(site: card_pages.Site) -> dict:
        script = site.files[card_pages.SCRIPT]
        return json.loads(script.split("var moves = ", 1)[1].split(", own = ", 1)[0])

    @staticmethod
    def elements(text: str) -> list[str]:
        import re

        return re.findall(r'<p class="atlas-moved" id="([^"]+)">This statement moved: <a href="([^"]+)">', text)

    def test_a_pure_folder_rename(self) -> None:
        # The folder's row and its statements' rows: a folder row moves the folder alone.
        site = self.site([leaf(f"{T}/card/main"), leaf(f"{T}/card/lemma")],
                         [card(1, f"{T}/card", ["main", "lemma"])],
                         *rename(f"{T}/old", f"{T}/card", 1, pages={"main": 10, "lemma": 11}))
        notice = site.files[f"roadmap/{T}/old/README.md"]
        self.assertIn('<p><a href="../card/index.html">Continue to the mathematical page</a></p>', notice)
        self.assertIn('<div class="bp-dag-viewer" data-page-href="../card/index.html" hidden></div>', notice)
        self.assertEqual(self.elements(notice), [("lemma", "../card/index.html#lemma"),
                                                 ("main", "../card/index.html#main")])
        # The elements serve a reader without JavaScript, so no refresh leaves them unread.
        self.assertNotIn("http-equiv", notice)
        # Its old explorer page leads where render's notices for live folders lead: to its page, now the card's.
        explorer = site.files[f"dependencies/scopes/{T}/old.md"]
        self.assertIn('<a href="../../../../../roadmap/A/f/t/card/index.html">', explorer)
        self.assertIn('<meta http-equiv="refresh"', explorer)
        # The explorer's table names every old address, the folder's and those of its statements, as the notices do.
        self.assertEqual(self.moves(site), {f"{T}/old": f"{T}/card", f"{T}/old/main": f"{T}/card/main",
                                            f"{T}/old/lemma": f"{T}/card/lemma"})
        self.assertIn('<a href="../card/index.html#main">', site.files[f"roadmap/{T}/old/main.md"])
        # The pages an old explorer link reaches load the rewrite first: the folders above the old address, and where
        # the folder went.
        self.assertEqual(set(site.head), {f"roadmap/{path}index.html" for path in ("", "A/", "A/f/", f"{T}/",
                                                                                    f"{T}/card/")})
        self.assertEqual(site.head[f"roadmap/{T}/index.html"],
                         '<script src="../../../../javascripts/atlas-card-moves.js"></script>')

    def test_a_merge_whose_source_folder_vanishes(self) -> None:
        site = self.site([leaf(f"{T}/a/a-main"), leaf(f"{T}/a/a-z")], [card(1, f"{T}/a", ["a-main", "a-z"])],
                         {"page": f"{T}/z/z-main", "to": f"{T}/a/a-z", "article_id": af(31)},
                         {"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)})
        notice = site.files[f"roadmap/{T}/z/README.md"]
        # The vanished folder's notice leads to the card that replaced it; each old anchor to where its statement went.
        self.assertIn('<p><a href="../a/index.html">Continue to the mathematical page</a></p>', notice)
        self.assertEqual(self.elements(notice), [("z-main", "../a/index.html#a-z")])
        self.assertEqual(self.moves(site), {f"{T}/z": f"{T}/a", f"{T}/z/z-main": f"{T}/a/a-z"})
        self.assertNotIn(f"roadmap/{T}/z/index.html", site.anchors)

    def test_a_split_that_keeps_its_source_folder(self) -> None:
        site = self.site([leaf(f"{T}/other"), leaf(f"{T}/c/x")], [card(1, f"{T}/c", ["x"])],
                         {"page": f"{T}/x", "to": f"{T}/c/x", "article_id": af(11)})
        # On the old folder page, which still exists: an element with the old anchor and a plain link.
        self.assertEqual(site.anchors, {f"roadmap/{T}/index.html": [("x", '<p class="atlas-moved" id="x">This '
                                                                          'statement moved: <a href="c/index.html#x">x'
                                                                          "</a>.</p>")]})
        # And at the statement's old page of its own, a notice: see test_every_old_route_shape_is_kept.
        self.assertEqual([path for path in site.files if path.startswith("roadmap/")], [f"roadmap/{T}/x.md"])
        self.assertEqual(self.moves(site), {f"{T}/x": f"{T}/c/x"})

    def test_every_old_route_shape_is_kept(self) -> None:
        # Render boxes a statement with a declaration kind on its folder's page and publishes any other as a page
        # of its own. A statement may gain or lose its kind when it moves or at any later revision, and the ledger
        # does not record which route it had: each old address keeps both, whatever its route is now.
        site = self.site([leaf(f"{T}/other"), leaf(f"{T}/c/was-planned"), leaf(f"{T}/c/now-planned", own_page=True),
                          leaf(f"{T}/c/boxed"), leaf(f"{T}/c/planned", own_page=True)],
                         [card(1, f"{T}/c", ["was-planned", "now-planned", "boxed", "planned"])],
                         *({"page": f"{T}/{name}", "to": f"{T}/c/{name}", "article_id": af(20 + number)}
                           for number, name in enumerate(("was-planned", "now-planned", "boxed", "planned"))))
        expected = {"was-planned": "c/index.html#was-planned", "now-planned": "c/now-planned.html",
                    "boxed": "c/index.html#boxed", "planned": "c/planned.html"}
        anchors = dict(self.elements("".join(element for _, element in site.anchors[f"roadmap/{T}/index.html"])))
        self.assertEqual(anchors, expected)
        for name, target in expected.items():
            with self.subTest(name):
                notice = site.files[f"roadmap/{T}/{name}.md"]
                self.assertIn(f'<p><a href="{target}">Continue to the mathematical page</a></p>', notice)
                self.assertIn(f'<meta http-equiv="refresh" content="0; url={target}">', notice)

    def test_the_move_of_a_leaf_that_had_no_id(self) -> None:
        # A planned page with no declaration kind is published as its own page; it got its id when it moved.
        site = self.site([leaf(f"{T}/c/p", own_page=True)], [card(1, f"{T}/c", ["p"])],
                         {"page": f"{T}/p", "to": f"{T}/c/p", "article_id": af(99)})
        notice = site.files[f"roadmap/{T}/p.md"]
        self.assertIn('<p><a href="c/p.html">Continue to the mathematical page</a></p>', notice)
        self.assertIn('<meta http-equiv="refresh" content="0; url=c/p.html">', notice)
        self.assertEqual([slug for slug, _ in site.anchors[f"roadmap/{T}/index.html"]], ["p"])

    def test_two_moves_of_one_page(self) -> None:
        site = self.site([leaf(f"{T}/c/m")], [card(1, f"{T}/c", ["m"])],
                         {"page": f"{T}/m", "to": f"{T}/mid/m", "article_id": af(10)},
                         {"page": f"{T}/mid/m", "to": f"{T}/c/m", "article_id": af(10)})
        # Both old addresses lead to the last one; the folder in between is gone and leads to its nearest live
        # folder, with the old anchor.
        self.assertEqual(self.elements(site.anchors[f"roadmap/{T}/index.html"][0][1]), [("m", "c/index.html#m")])
        notice = site.files[f"roadmap/{T}/mid/README.md"]
        self.assertIn('<p><a href="../index.html">Continue', notice)
        self.assertEqual(self.elements(notice), [("m", "../c/index.html#m")])
        self.assertEqual(self.moves(site), {f"{T}/m": f"{T}/c/m", f"{T}/mid/m": f"{T}/c/m", f"{T}/mid": T})

    def test_two_siblings_with_the_same_file_name(self) -> None:
        # Two topics each had a `lemma`; both moved into one card, so one was renamed. Each old anchor leads to its own.
        site = self.site([leaf("A/f/t1/x"), leaf("A/f/t2/y"), leaf("A/f/c/lemma"), leaf("A/f/c/lemma-2")],
                         [card(1, "A/f/c", ["lemma", "lemma-2"])],
                         {"page": "A/f/t1/lemma", "to": "A/f/c/lemma", "article_id": af(11)},
                         {"page": "A/f/t2/lemma", "to": "A/f/c/lemma-2", "article_id": af(12)})
        self.assertEqual(self.elements(site.anchors["roadmap/A/f/t1/index.html"][0][1]),
                         [("lemma", "../c/index.html#lemma")])
        self.assertEqual(self.elements(site.anchors["roadmap/A/f/t2/index.html"][0][1]),
                         [("lemma", "../c/index.html#lemma-2")])
        self.assertEqual(self.moves(site), {"A/f/t1/lemma": "A/f/c/lemma", "A/f/t2/lemma": "A/f/c/lemma-2"})

    def test_cards_replaced_in_place_one_after_the_other(self) -> None:
        # Card 8 was replaced in place by card 9, and card 9 in place by card 1: three ids, one folder, which
        # still exists. Nothing moved, so nothing redirects, and the card shows.
        rows = ({"card": af(8), "folder": f"{T}/z", "replaced_by": af(9)},
                {"card": af(9), "folder": f"{T}/z", "replaced_by": af(1)})
        site = self.site([leaf(f"{T}/z/z-main")], [card(1, f"{T}/z", ["z-main"])], *rows)
        self.assertEqual(list(site.blocks), [f"roadmap/{T}/z/index.html"])
        self.assertEqual((site.anchors, site.files, site.head), ({}, {}, {}))

    def test_a_folder_gone_after_replacements_in_place_leads_to_the_last_card(self) -> None:
        # Then card 1 merged into card 2: the folder is gone, and its old anchors lead to where each statement went.
        rows = ({"card": af(8), "folder": f"{T}/z", "replaced_by": af(9)},
                {"card": af(9), "folder": f"{T}/z", "replaced_by": af(1)},
                {"page": f"{T}/z/z-main", "to": f"{T}/a/a-z", "article_id": af(31)},
                {"page": f"{T}/z/z-lemma", "to": f"{T}/a/z-lemma", "article_id": af(32)},
                {"card": af(1), "folder": f"{T}/z", "replaced_by": af(2)})
        site = self.site([leaf(f"{T}/a/a-main"), leaf(f"{T}/a/a-z"), leaf(f"{T}/a/z-lemma", own_page=True)],
                         [card(2, f"{T}/a", ["a-main", "a-z", "z-lemma"])], *rows)
        notice = site.files[f"roadmap/{T}/z/README.md"]
        self.assertIn('<p><a href="../a/index.html">Continue to the mathematical page</a></p>', notice)
        self.assertEqual(self.elements(notice), [("z-lemma", "../a/z-lemma.html"), ("z-main", "../a/index.html#a-z")])
        self.assertIn('<a href="../a/index.html#a-z">', site.files[f"roadmap/{T}/z/z-main.md"])
        self.assertEqual(self.moves(site), {f"{T}/z": f"{T}/a", f"{T}/z/z-main": f"{T}/a/a-z",
                                            f"{T}/z/z-lemma": f"{T}/a/z-lemma"})

    def assertKept(self, site: card_pages.Site, folders: dict[str, str], statements: dict[str, str]) -> None:
        """Every old address keeps leading where it should, by each route shape: in the explorer's table the site
        serves; an old folder by a notice at its page and at its old explorer page; an old statement by a notice at
        its page of its own and by its old anchor, on its old folder's page or in that folder's notice."""
        self.assertEqual(self.moves(site), {**folders, **statements})
        for old, new in folders.items():
            with self.subTest(old=old):
                page = f"roadmap/{old}/index.html"
                target = posixpath.relpath(f"roadmap/{new}/index.html", posixpath.dirname(page))
                self.assertIn(f'<p><a href="{target}">Continue', site.files[f"roadmap/{old}/README.md"])
                self.assertIn(f"dependencies/scopes/{old}.md", site.files)
        for old, new in statements.items():
            with self.subTest(old=old):
                box = f"roadmap/{new.rsplit('/', 1)[0]}/index.html#{new.rsplit('/', 1)[1]}"
                target = posixpath.relpath(box, posixpath.dirname(f"roadmap/{old}.html"))
                self.assertIn(f'<p><a href="{target}">Continue', site.files[f"roadmap/{old}.md"])
                folder, slug = old.rsplit("/", 1)
                holder = (site.files.get(f"roadmap/{folder}/README.md", "")
                          + "".join(element for _, element in site.anchors.get(f"roadmap/{folder}/index.html", [])))
                target = posixpath.relpath(box, f"roadmap/{folder}")
                self.assertIn(f'<p class="atlas-moved" id="{slug}">This statement moved: <a href="{target}">', holder)

    def test_a_child_folder_leaves_a_renamed_folder(self) -> None:
        # old/sub/x; the folder old is renamed new; then its child new/sub moves to elsewhere. Every address the
        # child and its statement had, before and after the rename, leads to where they are now.
        site = self.site([leaf(f"{T}/new/kept"), leaf(f"{T}/elsewhere/x")], [card(1, f"{T}/elsewhere", ["x"])],
                         *rename(f"{T}/old", f"{T}/new", 50, pages={"kept": 11}, folders={"sub": 1}),
                         {"page": f"{T}/old/sub/x", "to": f"{T}/new/sub/x", "article_id": af(10)},
                         *rename(f"{T}/new/sub", f"{T}/elsewhere", 1, pages={"x": 10}))
        self.assertKept(site, {f"{T}/old": f"{T}/new", f"{T}/old/sub": f"{T}/elsewhere",
                               f"{T}/new/sub": f"{T}/elsewhere"},
                        {f"{T}/old/kept": f"{T}/new/kept", f"{T}/old/sub/x": f"{T}/elsewhere/x",
                         f"{T}/new/sub/x": f"{T}/elsewhere/x"})

    def test_a_child_card_leaves_a_renamed_folder_and_is_retired(self) -> None:
        # old/sub is a card; old is renamed new; then new/sub's statement moves into the card c, and new/sub is
        # retired, replaced by c.
        site = self.site([leaf(f"{T}/new/kept"), leaf(f"{T}/c/c-main"), leaf(f"{T}/c/x")],
                         [card(1, f"{T}/c", ["c-main", "x"])],
                         *rename(f"{T}/old", f"{T}/new", 50, pages={"kept": 11}, folders={"sub": 5}),
                         {"page": f"{T}/old/sub/x", "to": f"{T}/new/sub/x", "article_id": af(10)},
                         {"page": f"{T}/new/sub/x", "to": f"{T}/c/x", "article_id": af(10)},
                         {"card": af(5), "folder": f"{T}/new/sub", "replaced_by": af(1)})
        self.assertKept(site, {f"{T}/old": f"{T}/new", f"{T}/old/sub": f"{T}/c", f"{T}/new/sub": f"{T}/c"},
                        {f"{T}/old/kept": f"{T}/new/kept", f"{T}/old/sub/x": f"{T}/c/x", f"{T}/new/sub/x": f"{T}/c/x"})

    def test_a_statement_leaves_between_two_renames(self) -> None:
        # old is renamed mid; mid/x moves to elsewhere/y; mid is renamed new. old/x leads to elsewhere/y, never to
        # new/x, which never existed.
        site = self.site([leaf(f"{T}/new/z"), leaf(f"{T}/elsewhere/e"), leaf(f"{T}/elsewhere/y")],
                         [card(2, f"{T}/elsewhere", ["e", "y"])],
                         *rename(f"{T}/old", f"{T}/mid", 50, pages={"z": 11, "x": 10}),
                         {"page": f"{T}/mid/x", "to": f"{T}/elsewhere/y", "article_id": af(10)},
                         *rename(f"{T}/mid", f"{T}/new", 50, pages={"z": 11}))
        self.assertKept(site, {f"{T}/old": f"{T}/new", f"{T}/mid": f"{T}/new"},
                        {f"{T}/old/z": f"{T}/new/z", f"{T}/mid/z": f"{T}/new/z", f"{T}/old/x": f"{T}/elsewhere/y",
                         f"{T}/mid/x": f"{T}/elsewhere/y"})
        self.assertNotIn(f"roadmap/{T}/new/x.md", site.files)

    def test_a_page_added_after_its_folder_moved_gets_no_old_address(self) -> None:
        # One change renamed old to new with its statement x; a later one added fresh to new, with no row, as an
        # addition needs none. old/fresh never existed, so nothing leads from it.
        site = self.site([leaf(f"{T}/new/x"), leaf(f"{T}/new/fresh"), leaf(f"{T}/c/c-main")],
                         [card(1, f"{T}/c", ["c-main"])], *rename(f"{T}/old", f"{T}/new", 50, pages={"x": 10}))
        self.assertKept(site, {f"{T}/old": f"{T}/new"}, {f"{T}/old/x": f"{T}/new/x"})
        self.assertNotIn(f"roadmap/{T}/old/fresh.md", site.files)
        self.assertNotIn('id="fresh"', site.files[f"roadmap/{T}/old/README.md"])

    def test_a_folder_row_carries_nothing_inside_the_folder(self) -> None:
        # The folder row alone: the statement inside it has no row, so no address of it is inferred (the strict
        # check refuses such a ledger: the statement moved and no row leads there).
        site = self.site([leaf(f"{T}/new/x"), leaf(f"{T}/c/c-main")], [card(1, f"{T}/c", ["c-main"])],
                         *rename(f"{T}/old", f"{T}/new", 50))
        self.assertEqual(self.moves(site), {f"{T}/old": f"{T}/new"})
        self.assertNotIn(f"roadmap/{T}/old/x.md", site.files)

    def test_a_ledger_that_leads_nowhere_the_site_publishes_shows_no_card_data(self) -> None:
        for rows in ([{"page": f"{T}/x", "to": f"{T}/c/gone", "article_id": af(11)}],
                     [{"folder": f"{T}/old", "to": f"{T}/gone", "article_id": af(1)}],
                     [{"card": af(7), "folder": f"{T}/z", "replaced_by": af(8)}],
                     [{"card": af(7), "folder": f"{T}/z", "replaced_by": af(8)},
                      {"card": af(8), "folder": f"{T}/z", "replaced_by": af(7)}],
                     [{"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)},
                      {"card": af(7), "folder": f"{T}/y", "replaced_by": af(1)}],
                     [{"page": f"{T}/x", "to": f"{T}/y", "article_id": af(11)},
                      {"page": f"{T}/y", "to": f"{T}/x", "article_id": af(11)}],
                     [{"move": f"{T}/x"}]):
            with self.subTest(rows=rows), self.assertRaises(card_pages.CardDataError):
                self.site([leaf(f"{T}/c/x")], [card(1, f"{T}/c", ["x"])], *rows)

    @staticmethod
    def retired(entries: list[dict], replacements: dict[str, tuple[str, str]], *rows: dict) -> card_pages.Site:
        """The redirects of ``rows``, with no card, the ledger check giving each retirement's replacement."""
        with tempfile.TemporaryDirectory() as docs:
            return card_pages.build(rollup([]), index(*entries), ledger(*rows), Path(docs), listed={},
                                    replacements=replacements)

    def test_a_retired_statement_leads_to_its_replacement(self) -> None:
        # The node T/node was expanded and its page deleted; its replacement, a statement boxed on the topic's page or
        # one with a page of its own. Both routes the node may have had lead there.
        retire = {"statement": af(20), "page": f"{T}/node", "replaced_by": af(21)}
        for replacement, own_page, target in ((f"{T}/node-a", False, "index.html#node-a"),
                                              (f"{T}/node-b", True, "node-b.html")):
            with self.subTest(replacement):
                site = self.retired([leaf(replacement, own_page=own_page)], {af(21): ("page", replacement)}, retire)
                notice = site.files[f"roadmap/{T}/node.md"]
                self.assertIn(f'<p><a href="{target}">Continue to the mathematical page</a></p>', notice)
                anchor = target.removeprefix("index.html")
                self.assertEqual(self.elements(site.anchors[f"roadmap/{T}/index.html"][0][1]), [("node", anchor)])
                self.assertEqual(self.moves(site), {f"{T}/node": replacement})

    def test_a_retired_statement_may_lead_to_a_folder(self) -> None:
        # Expanded into a folder of its own name, whose folder page replaces it, or into a folder elsewhere. An
        # explorer link to the node's address names the folder of its own name already, and needs no rewrite.
        retire = {"statement": af(20), "page": f"{T}/node", "replaced_by": af(25)}
        for replacement, target in ((f"{T}/node", "node/index.html"), (f"{T}/elsewhere", "elsewhere/index.html")):
            with self.subTest(replacement):
                site = self.retired([leaf(f"{replacement}/part"), folder(replacement, "Replacement")],
                                    {af(25): ("folder", replacement)}, retire)
                notice = site.files[f"roadmap/{T}/node.md"]
                self.assertIn(f'<p><a href="{target}">Continue to the mathematical page</a></p>', notice)
                self.assertIn(f'<meta http-equiv="refresh" content="0; url={target}">', notice)
                self.assertEqual(self.elements(site.anchors[f"roadmap/{T}/index.html"][0][1]), [("node", target)])
                if replacement == f"{T}/node":
                    self.assertEqual((card_pages.SCRIPT in site.files, site.head), (False, {}))
                else:
                    self.assertEqual(self.moves(site), {f"{T}/node": replacement})

    def test_a_retired_statement_s_replacements_are_followed(self) -> None:
        # node-a replaced the node and was retired in turn, for node-b; and a statement replaced by card 7, which was
        # retired for card 1.
        site = self.retired([leaf(f"{T}/node-b")], {af(22): ("page", f"{T}/node-b")},
                            {"statement": af(20), "page": f"{T}/node", "replaced_by": af(21)},
                            {"statement": af(21), "page": f"{T}/node-a", "replaced_by": af(22)})
        self.assertEqual(self.moves(site), {f"{T}/node": f"{T}/node-b", f"{T}/node-a": f"{T}/node-b"})
        site = self.retired([leaf(f"{T}/c/c-main"), folder(f"{T}/c", "Card C")], {af(1): ("folder", f"{T}/c")},
                            {"statement": af(20), "page": f"{T}/node", "replaced_by": af(7)},
                            {"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)})
        self.assertEqual(self.moves(site), {f"{T}/node": f"{T}/c", f"{T}/z": f"{T}/c"})

    def test_a_statement_replaced_in_place_keeps_the_route_its_replacement_lacks(self) -> None:
        # The node T/node is replaced by a new statement at its address, whose route may be the other form: the node's
        # old route of that form leads to it, and its own route is left alone, never redirected to itself.
        retire = {"statement": af(20), "page": f"{T}/node", "replaced_by": af(24)}
        # Boxed: the node may have had a page of its own, which now leads to the box.
        site = self.retired([leaf(f"{T}/node"), leaf(f"{T}/other")], {af(24): ("page", f"{T}/node")}, retire)
        self.assertEqual(list(site.files), [f"roadmap/{T}/node.md"])
        self.assertIn('<p><a href="index.html#node">Continue to the mathematical page</a></p>',
                      site.files[f"roadmap/{T}/node.md"])
        self.assertEqual((site.anchors, site.head), ({}, {}))
        # On a page of its own: the node may have been boxed on the topic's page, whose old anchor now leads to the
        # page; no notice takes the page's place.
        site = self.retired([leaf(f"{T}/node", own_page=True), leaf(f"{T}/other")],
                            {af(24): ("page", f"{T}/node")}, retire)
        self.assertEqual(site.files, {})
        self.assertEqual(self.elements(site.anchors[f"roadmap/{T}/index.html"][0][1]), [("node", "node.html")])
        self.assertEqual(site.head, {})

    def test_an_address_has_one_owner(self) -> None:
        # Two statements retired at one address in favour of different articles, whatever their order, and two cards
        # retired at one folder likewise: two owners, no redirect.
        entries = [leaf(f"{T}/a"), leaf(f"{T}/b"), leaf(f"{T}/c/c-main"), leaf(f"{T}/d/d-main"),
                   folder(f"{T}/c", "Card C"), folder(f"{T}/d", "Card D")]
        replacements = {af(21): ("page", f"{T}/a"), af(22): ("page", f"{T}/b"), af(1): ("folder", f"{T}/c"),
                        af(2): ("folder", f"{T}/d")}
        for name, rows in (
            ("two statements", [{"statement": af(20), "page": f"{T}/gone", "replaced_by": af(21)},
                                {"statement": af(30), "page": f"{T}/gone", "replaced_by": af(22)}]),
            ("two statements, the other way", [{"statement": af(30), "page": f"{T}/gone", "replaced_by": af(22)},
                                               {"statement": af(20), "page": f"{T}/gone", "replaced_by": af(21)}]),
            ("two cards", [{"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)},
                           {"card": af(8), "folder": f"{T}/z", "replaced_by": af(2)}]),
        ):
            with self.subTest(name), self.assertRaises(card_pages.CardDataError) as refused:
                self.retired(entries, replacements, *rows)
            self.assertIn("an address has one owner", str(refused.exception))
        # One history at one address, each retired in place by the next, leads to the last replacement.
        site = self.retired(entries, replacements, {"statement": af(20), "page": f"{T}/gone", "replaced_by": af(30)},
                            {"statement": af(30), "page": f"{T}/gone", "replaced_by": af(22)})
        self.assertEqual(self.moves(site), {f"{T}/gone": f"{T}/b"})

    def test_a_replacement_that_moves_into_the_retired_address(self) -> None:
        # The node is retired in favour of the lemma, which then moves into the node's address: the lemma's old
        # address leads there, and the node's keeps the route form the lemma lacks.
        site = self.retired([leaf(f"{T}/node", own_page=True)], {af(21): ("page", f"{T}/node")},
                            {"statement": af(20), "page": f"{T}/node", "replaced_by": af(21)},
                            {"page": f"{T}/lemma", "to": f"{T}/node", "article_id": af(21)})
        self.assertEqual(self.moves(site), {f"{T}/lemma": f"{T}/node"})
        self.assertEqual(sorted(site.files), [card_pages.SCRIPT, f"roadmap/{T}/lemma.md"])
        self.assertEqual(sorted(slug for slug, _ in site.anchors[f"roadmap/{T}/index.html"]), ["lemma", "node"])

    def test_a_retired_statement_needs_its_replacement_and_a_well_formed_row(self) -> None:
        retire = {"statement": af(20), "page": f"{T}/node", "replaced_by": af(21)}
        entries = [leaf(f"{T}/node-a"), leaf(f"{T}/c/c-main")]
        for name, replacements, rows in (
            ("a replacement not listed", {}, [retire]),
            ("a page the site does not publish", {af(21): ("page", f"{T}/gone")}, [retire]),
            ("a page given as a folder", {af(21): ("folder", f"{T}/node-a")}, [retire]),
            ("a card's replacement that is a page", {af(1): ("page", f"{T}/c/c-main")},
             [{"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)}]),
            ("replacements that go round", {}, [retire, {"statement": af(21), "page": f"{T}/node-a",
                                                         "replaced_by": af(20)}]),
            ("a malformed id", {af(21): ("page", f"{T}/node-a")}, [{**retire, "statement": "af_20"}]),
            ("a page address with `.md`", {af(21): ("page", f"{T}/node-a")}, [{**retire, "page": f"{T}/node.md"}]),
            ("a statement retired twice", {af(21): ("page", f"{T}/node-a")}, [retire, retire]),
            ("a statement retired as a card too", {af(21): ("page", f"{T}/node-a")},
             [retire, {"card": af(20), "folder": f"{T}/z", "replaced_by": af(1)}]),
            ("an address that moved too", {af(21): ("page", f"{T}/node-a")},
             [retire, {"page": f"{T}/node", "to": f"{T}/node-a", "article_id": af(21)}]),
            ("an address a retired card had", {af(21): ("page", f"{T}/node-a"), af(1): ("folder", f"{T}/c")},
             [retire, {"card": af(7), "folder": f"{T}/node", "replaced_by": af(1)}]),
        ):
            with self.subTest(name), self.assertRaises(card_pages.CardDataError):
                self.retired(entries + [folder(f"{T}/c", "Card C")], replacements, *rows)
        # Another article at the retired address, live there or moved in.
        for rows in ([retire], [retire, {"page": f"{T}/q", "to": f"{T}/node", "article_id": af(23)}]):
            with self.subTest(rows=rows), self.assertRaises(card_pages.CardDataError) as refused:
                self.retired(entries + [leaf(f"{T}/node")], {af(21): ("page", f"{T}/node-a")}, *rows)
            self.assertIn(f"the last address {T}/node of", str(refused.exception))

    def test_an_old_anchor_that_names_an_element_of_the_page_is_left_to_it(self) -> None:
        site = self.site([leaf(f"{T}/other"), leaf(f"{T}/c/idea"), leaf(f"{T}/c/x")],
                         [card(1, f"{T}/c", ["idea", "x"])],
                         {"page": f"{T}/idea", "to": f"{T}/c/idea", "article_id": af(11)},
                         {"page": f"{T}/x", "to": f"{T}/c/x", "article_id": af(12)})
        page = ('<div class="bp-reading-source"><h1>T</h1><h2 id="idea">Idea</h2><p>Text.</p></div>'
                '<div class="bp-dag-viewer"></div>')
        with self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged:
            shown = self.render(site, f"roadmap/{T}/index.html", page)
        self.assertEqual([slug for slug, _ in self.elements(shown)], ["x"])
        # The ambiguity is reported, not guessed: the page's own element keeps the id, and the statement keeps
        # its old page of its own and its explorer link.
        self.assertEqual(site.collisions, [f"roadmap/{T}/index.html#idea"])
        self.assertIn(f"roadmap/{T}/index.html#idea now names an element of that page", logged.output[0])
        self.assertIn(f"roadmap/{T}/idea.md", site.files)
        self.assertIn(f"<script>{card_pages.FOLLOW}</script></div></div><div class=\"bp-dag-viewer\">", shown)

    @staticmethod
    def render(site: card_pages.Site, path: str, content: str) -> str:
        import types

        card_pages._site = site
        try:
            page = types.SimpleNamespace(file=types.SimpleNamespace(dest_uri=path))
            return card_pages.on_page_content(content, page=page, config=None, files=None)
        finally:
            card_pages._site = None

    def test_the_block_goes_before_the_first_section_of_the_reading(self) -> None:
        library = Library()
        site = library.build()
        page = ('<div class="bp-dag-viewer" hidden><h2>Frame</h2></div><div class="bp-reading-source">'
                '<script>var a = "<div><h2>";</script><h1>X</h1><p>Opening.</p><div class="bp-progress-overview">'
                "</div><h2 id=\"idea\">Idea</h2></div>")
        shown = self.render(site, f"roadmap/{T}/x/index.html", page)
        self.assertIn('<div class="bp-progress-overview"></div><div class="atlas-card">', shown)
        self.assertTrue(shown.endswith('</div><h2 id="idea">Idea</h2></div>'))


def node_folder(node_id: str, title: str | None = None, transparent: bool = False) -> dict:
    """An index entry of a folder whose folder page holds nothing below it, as pinned render writes one: a node at
    the folder's own page, plain or transparent."""
    return {"id": node_id, "kind": "node", "route": f"../roadmap/{node_id}/index.html",
            "title": title or node_id.rsplit("/", 1)[-1], "scope": node_id.rsplit("/", 1)[0], "status": "planned",
            "result": False, **({"navigation": "transparent"} if transparent else {})}


class LeftoverFolderPageTests(unittest.TestCase):
    """A folder page left in the site source when everything below it moved away, which render indexes as a node at the
    folder's own page, plain or transparent (as TheoryOfComputation/not-yet-classified/part-03/part-18 was left), or
    does not index at all, is there: it keeps its own address and its page, so no route is inferred or kept for it,
    and its old explorer page, which render no longer writes, leads to its page. The search for gone folders above an
    address a row leaves goes on past it. What is bound to a folder render indexes leads to its page; what is bound to
    one it does not index leads to the nearest folder render publishes above it (history()). Deleted, the same folder
    is gone, and its inferred route is kept."""

    LINKS = {"_defaults.json": b'{"object": {"type": "lean", "uri": "../.."}}\n'}
    BASE = [leaf(f"{T}/s/x"), leaf(f"{T}/s/y"), leaf(f"{T}/keep")]
    # The folder p/q moved to s with its page x, as a folder row moves a folder alone.
    ROWS = [{"folder": f"{T}/p/q", "to": f"{T}/s", "article_id": af(1)},
            {"page": f"{T}/p/q/x", "to": f"{T}/s/x", "article_id": af(10)}]
    SHAPES = {"plain": lambda folder: [node_folder(folder)],
              "transparent": lambda folder: [node_folder(folder, None, True)], "unindexed": lambda folder: []}

    def assembled(self, rows: list[dict], sources: tuple[str, ...] = (), entries: list[dict] | None = None,
                  replacements: dict[str, dict[str, str]] | None = None,
                  absent: tuple[str, ...] = ()) -> tuple[card_pages.Site, str | None]:
        """What the hook adds, and why it keeps no moved address, on a checkout whose ledger is ``rows``, with the
        receipt of that commit giving ``replacements``, render's index of BASE and ``entries`` but the folders
        ``absent``, which have no folder page, and the folder pages ``sources`` in the site source."""
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            git = ["git", "-C", str(root), "-c", "user.name=Test", "-c", "user.email=test@example.com"]
            subprocess.run([*git, "init", "-q"], check=True)
            subprocess.run([*git, "commit", "-q", "--allow-empty", "-m", "fixture"], check=True)
            commit = subprocess.run([*git, "rev-parse", "HEAD"], check=True, capture_output=True,
                                    text=True).stdout.strip()
            text = ledger(*rows)
            made = receipt(commit, text, {}, self.LINKS, replacements=replacements)
            nodes = index(*self.BASE, *(entries or []))
            nodes["nodes"] = [entry for entry in nodes["nodes"] if entry["id"] not in absent]
            files = {"site-src/dependencies/index.json": json.dumps(nodes).encode(),
                     "scripts/card-moves.jsonl": text.encode(), "build/card-moves.json": json.dumps(made).encode(),
                     **{f"blueprint/links/{name}": data for name, data in self.LINKS.items()},
                     **{f"site-src/roadmap/{folder}/README.md": b"# Left\n" for folder in sources}}
            for path, content in files.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(content)
            site, _, unkept = card_pages.assemble(root, root / "site-src")
            return site, unkept

    @staticmethod
    def link(text: str) -> str:
        return text.split('<p><a href="', 1)[1].split('"', 1)[0]

    def test_a_page_only_folder_keeps_its_page_and_its_old_explorer_page_leads_there(self) -> None:
        # The shape #9947 left: p keeps its folder page, with nothing below it. The site keeps both rows' addresses; p's
        # page keeps p's, with no route and no notice over it; its old explorer page leads to its page, render writing
        # none now. Both reader forms of the gone folder's address, <folder>/ and <folder>/index.html, are its notice's
        # (README.md in the site source), and a page's old address is its notice at <page>.html.
        for shape, entries in self.SHAPES.items():
            with self.subTest(shape):
                site, unkept = self.assembled(self.ROWS, (f"{T}/p",), entries(f"{T}/p"))
                self.assertIsNone(unkept)
                self.assertEqual(site.addresses, 2)
                self.assertEqual(RedirectTests.moves(site), {f"{T}/p/q": f"{T}/s", f"{T}/p/q/x": f"{T}/s/x"})
                self.assertNotIn(f"roadmap/{T}/p/README.md", site.files)
                self.assertEqual(self.link(site.files[f"dependencies/scopes/{T}/p.md"]),
                                 "../../../../../roadmap/A/f/t/p/index.html")
                self.assertEqual(self.link(site.files[f"roadmap/{T}/p/q/README.md"]), "../../s/index.html")
                self.assertEqual(self.link(site.files[f"roadmap/{T}/p/q/x.md"]), "../../s/index.html#x")

    def test_an_old_explorer_link_through_a_page_only_folder_is_rewritten(self) -> None:
        # The only row moves the page p/x out of p, whose folder page stays with nothing below it. A bookmark of p's old
        # explorer page with #node=A/f/t/p/x reaches p's page through its notice, which keeps the fragment; p's page
        # loads the explorer's rewrite table, which leads x to s/x and leaves p, a live node, as it is.
        rows = [{"page": f"{T}/p/x", "to": f"{T}/s/x", "article_id": af(10)}]
        for shape, entries in self.SHAPES.items():
            with self.subTest(shape):
                site, unkept = self.assembled(rows, (f"{T}/p",), entries(f"{T}/p"))
                self.assertIsNone(unkept)
                alias = site.files[f"dependencies/scopes/{T}/p.md"]
                self.assertEqual(self.link(alias), "../../../../../roadmap/A/f/t/p/index.html")
                self.assertIn("if(!e&&!to.hash)to.hash=location.hash", alias)
                self.assertEqual(site.head[f"roadmap/{T}/p/index.html"],
                                 '<script src="../../../../../javascripts/atlas-card-moves.js"></script>')
                self.assertEqual(RedirectTests.moves(site), {f"{T}/p/x": f"{T}/s/x"})
                self.assertNotIn(f"roadmap/{T}/p/README.md", site.files)

    def test_the_same_folder_page_deleted_is_inferred_and_kept(self) -> None:
        # The shape of #10866: p's folder page is gone too, and p leads to its nearest published folder, t.
        site, unkept = self.assembled(self.ROWS)
        self.assertIsNone(unkept)
        self.assertEqual(site.addresses, 3)
        self.assertEqual(RedirectTests.moves(site), {f"{T}/p": T, f"{T}/p/q": f"{T}/s", f"{T}/p/q/x": f"{T}/s/x"})
        self.assertEqual(self.link(site.files[f"roadmap/{T}/p/README.md"]), "../index.html")

    def test_what_is_bound_to_a_page_only_folder(self) -> None:
        # Below p: the gone folder g, which no row speaks of, held the page x. Indexed, p is where g leads; unindexed,
        # the explorer cannot select it, and g leads to t, the nearest folder render publishes. The page y that left p
        # itself keeps its old anchor on p's page; a folder row into p leads where g does.
        rows = [{"page": f"{T}/p/g/x", "to": f"{T}/s/x", "article_id": af(10)},
                {"page": f"{T}/p/y", "to": f"{T}/s/y", "article_id": af(11)}]
        for shape, entries in self.SHAPES.items():
            with self.subTest(shape):
                target = T if shape == "unindexed" else f"{T}/p"
                site, unkept = self.assembled(rows, (f"{T}/p",), entries(f"{T}/p"))
                self.assertIsNone(unkept)
                self.assertEqual(RedirectTests.moves(site), {f"{T}/p/g": target, f"{T}/p/g/x": f"{T}/s/x",
                                                             f"{T}/p/y": f"{T}/s/y"})
                notice = site.files[f"roadmap/{T}/p/g/README.md"]
                self.assertEqual(self.link(notice), "../../index.html" if shape == "unindexed" else "../index.html")
                self.assertEqual(RedirectTests.elements(notice), [("x", "../../s/index.html#x")])
                anchors = "".join(element for _, element in site.anchors[f"roadmap/{T}/p/index.html"])
                self.assertEqual(RedirectTests.elements(anchors), [("y", "../s/index.html#y")])
                self.assertNotIn(f"roadmap/{T}/p/README.md", site.files)
                site, unkept = self.assembled([{"folder": f"{T}/w", "to": f"{T}/p", "article_id": af(2)}], (f"{T}/p",),
                                              entries(f"{T}/p"))
                self.assertIsNone(unkept)
                self.assertEqual(RedirectTests.moves(site), {f"{T}/w": target})

    def test_a_gone_folder_above_a_page_only_folder_keeps_a_route(self) -> None:
        # e's folder page is gone and q's stays, holding nothing below it, as the page e/q/x left: the search for gone
        # folders goes on past q, so e keeps a route, to t, with its notice, its old explorer page and the explorer's
        # rewrite; q keeps its page and its old explorer page leads there. With q's folder page gone too, both lead
        # to t.
        rows = [{"page": f"{T}/e/q/x", "to": f"{T}/s/x", "article_id": af(10)}]
        for shape, entries in self.SHAPES.items():
            with self.subTest(shape):
                site, unkept = self.assembled(rows, (f"{T}/e/q",), entries(f"{T}/e/q"), absent=(f"{T}/e",))
                self.assertIsNone(unkept)
                self.assertEqual(RedirectTests.moves(site), {f"{T}/e": T, f"{T}/e/q/x": f"{T}/s/x"})
                self.assertEqual(self.link(site.files[f"roadmap/{T}/e/README.md"]), "../index.html")
                self.assertEqual(self.link(site.files[f"dependencies/scopes/{T}/e.md"]),
                                 "../../../../../roadmap/A/f/t/index.html")
                self.assertEqual(self.link(site.files[f"dependencies/scopes/{T}/e/q.md"]),
                                 "../../../../../../roadmap/A/f/t/e/q/index.html")
                self.assertNotIn(f"roadmap/{T}/e/q/README.md", site.files)
        site, unkept = self.assembled(rows)
        self.assertIsNone(unkept)
        self.assertEqual(RedirectTests.moves(site), {f"{T}/e": T, f"{T}/e/q": T, f"{T}/e/q/x": f"{T}/s/x"})

    def test_a_gone_folder_below_a_page_only_folder_leads_to_it(self) -> None:
        # The mirror: q's folder page is gone and e's stays, holding nothing below it. Indexed, e is where q leads.
        rows = [{"page": f"{T}/e/q/x", "to": f"{T}/s/x", "article_id": af(10)}]
        for shape, entries in self.SHAPES.items():
            with self.subTest(shape):
                site, unkept = self.assembled(rows, (f"{T}/e",), entries(f"{T}/e"))
                self.assertIsNone(unkept)
                target = T if shape == "unindexed" else f"{T}/e"
                self.assertEqual(RedirectTests.moves(site), {f"{T}/e/q": target, f"{T}/e/q/x": f"{T}/s/x"})
                self.assertEqual(self.link(site.files[f"roadmap/{T}/e/q/README.md"]),
                                 "../../index.html" if shape == "unindexed" else "../index.html")
                self.assertNotIn(f"roadmap/{T}/e/README.md", site.files)

    def test_no_explorer_link_is_rewritten_for_an_address_render_publishes(self) -> None:
        # A statement page holds the address of the folder e that the page e/x left: e's old folder page leads to t,
        # but the explorer's #node=A/f/t/e is the live statement's, and is never rewritten.
        site, unkept = self.assembled([{"page": f"{T}/e/x", "to": f"{T}/s/x", "article_id": af(10)}], (),
                                      [leaf(f"{T}/e", own_page=True)])
        self.assertIsNone(unkept)
        self.assertEqual(RedirectTests.moves(site), {f"{T}/e/x": f"{T}/s/x"})
        self.assertEqual(self.link(site.files[f"roadmap/{T}/e/README.md"]), "../index.html")

    def test_a_retirement_may_be_replaced_by_a_page_only_folder(self) -> None:
        # The statement old is retired for the folder p, whose folder page holds nothing below it once the page p/e
        # left: render indexes p as a node at its page, which is where old leads; the unrelated move is kept too.
        rows = [{"statement": af(11), "page": f"{T}/old", "replaced_by": af(41)},
                {"page": f"{T}/p/e", "to": f"{T}/s/y", "article_id": af(10)}]
        replacements = {af(41): {"kind": "folder", "node": f"{T}/p"}}
        for shape in ("plain", "transparent"):
            with self.subTest(shape):
                site, unkept = self.assembled(rows, (f"{T}/p",), self.SHAPES[shape](f"{T}/p"), replacements)
                self.assertIsNone(unkept)
                self.assertEqual(RedirectTests.moves(site), {f"{T}/old": f"{T}/p", f"{T}/p/e": f"{T}/s/y"})
                self.assertEqual(self.link(site.files[f"roadmap/{T}/old.md"]), "p/index.html")
        # A replacement render publishes no page for, unindexed or absent, still keeps no moved address.
        for sources in ((f"{T}/p",), ()):
            site, unkept = self.assembled(rows, sources, [], replacements)
            self.assertEqual(unkept, f"{card_pages.LEDGER}: a retired statement's replacements end at {af(41)}, whose "
                                     f"folder {T}/p the site does not publish")


class ReceiptTests(unittest.TestCase):
    """The moved addresses are kept only with the ledger check's receipt of this commit, of its ledger and of its
    annotations, which places each card the history leads to; card data, which they never need, is shown only when its
    cards are the receipt's complete list. One history: card 7, retired at a folder z that is gone, replaced by card 1,
    which the receipt places at a; and a moved page."""

    ENTRIES = [leaf(f"{T}/a/a-main"), leaf(f"{T}/a/lemma"), leaf(f"{T}/b/b-main")]
    ROWS = ledger({"page": f"{T}/lemma", "to": f"{T}/a/lemma", "article_id": af(11)},
                  {"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)})
    CARDS = {af(1): f"{T}/a", af(2): f"{T}/b"}
    LINKS = {"A.jsonl": b'{"subject": [{"type": "generic", "uri": "../roadmap/A/f/t/a/README.md"}]}\n',
             "_defaults.json": b'{"object": {"type": "lean", "uri": "../.."}}\n'}
    MOVES = {f"{T}/z": f"{T}/a", f"{T}/lemma": f"{T}/a/lemma"}
    NO_DATA = "there is no build/cards.json (the rollup writes none when the strict check fails)"
    STILL = "::warning title=Card data not shown::{}; moved addresses are still kept\n"

    def hook(self, data=None, change=None, rows: str = ROWS,
             fragments: dict[str, str] | None = None) -> tuple[card_pages.Site | None, str]:
        """Run the hook as under GitHub Actions on a checkout with the ledger's frozen ``rows`` and ``fragments`` (by
        name), the links folder LINKS, the rollup ``data`` gives for the commit being built, and the receipt of that
        commit, ledger and links folder with the cards CARDS, which ``change`` may alter (``change(receipt, root)``; a
        receipt it returns as text is written as it is, and None writes none): the site the hook keeps, and what it
        prints."""
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            git = ["git", "-C", str(root), "-c", "user.name=Test", "-c", "user.email=test@example.com"]
            subprocess.run([*git, "init", "-q"], check=True)
            subprocess.run([*git, "commit", "-q", "--allow-empty", "-m", "fixture"], check=True)
            commit = subprocess.run([*git, "rev-parse", "HEAD"], check=True, capture_output=True,
                                    text=True).stdout.strip()
            parts = [("scripts/card-moves.jsonl", rows.encode()),
                     *((f"scripts/card-moves.d/{name}", text.encode())
                       for name, text in sorted((fragments or {}).items()))]
            files = {"site-src/dependencies/index.json": json.dumps(index(*self.ENTRIES)).encode(), **dict(parts),
                     **{f"blueprint/links/{name}": data for name, data in self.LINKS.items()}}
            if data is not None:
                files["build/cards.json"] = json.dumps(data(commit)).encode()
            for path, content in files.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(content)
            made = receipt(commit, parts, dict(self.CARDS), self.LINKS)
            if change is not None:
                made = change(made, root)
            if made is not None:
                (root / "build").mkdir(exist_ok=True)
                (root / "build" / "card-moves.json").write_text(made if isinstance(made, str) else json.dumps(made))
            config = types.SimpleNamespace(config_file_path=str(root / "mkdocs.yml"), docs_dir=str(root / "site-src"),
                                           extra_css=[])
            printed = io.StringIO()
            with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(root / "s.md")}), \
                    contextlib.redirect_stdout(printed), self.assertLogs("mkdocs.hooks.card_pages", "INFO"):
                card_pages.on_config(config)
            site, card_pages._site = card_pages._site, None
            return site, printed.getvalue()

    def assertMoves(self, site: card_pages.Site | None) -> None:
        self.assertIsNotNone(site)
        self.assertEqual(RedirectTests.moves(site), self.MOVES)
        self.assertIn('<p><a href="../a/index.html">Continue to the mathematical page</a></p>',
                      site.files[f"roadmap/{T}/z/README.md"])
        self.assertEqual([slug for slug, _ in site.anchors[f"roadmap/{T}/index.html"]], ["lemma"])

    def test_the_four_states_of_card_data(self) -> None:
        a, b = (lambda folder, pages: card(1, folder, pages)), (lambda: card(2, f"{T}/b", ["b-main"]))
        # No rollup: both addresses are kept, the retired card's leading to a, and no card is shown.
        site, printed = self.hook()
        self.assertMoves(site)
        self.assertEqual((site.blocks, printed), ({}, self.STILL.format(self.NO_DATA)))
        # A complete rollup, which places card 1 at a, as the receipt does: its cards, and the same addresses.
        site, printed = self.hook(lambda commit: rollup([a(f"{T}/a", ["a-main", "lemma"]), b()], commit=commit))
        self.assertMoves(site)
        self.assertEqual((sorted(site.blocks), printed),
                         ([f"roadmap/{T}/a/index.html", f"roadmap/{T}/b/index.html"], ""))
        # A consistent rollup with no card, and one that places card 1 at the published b: the same addresses, z
        # still leading to a, and no card, as the rollup is not the receipt's list.
        for data, reason in (
                (lambda commit: rollup([], commit=commit),
                 f"the rollup has no card {af(1)}, which build/card-moves.json places at {T}/a"),
                (lambda commit: rollup([a(f"{T}/b", ["b-main"])], commit=commit),
                 f"the rollup places {af(1)} at {T}/b, but build/card-moves.json places it at {T}/a")):
            with self.subTest(reason):
                site, printed = self.hook(data)
                self.assertMoves(site)
                self.assertEqual((site.blocks, printed), ({}, self.STILL.format(reason)))
        # An ordinary card error: the addresses are kept, and no card is shown.
        site, printed = self.hook(lambda commit: rollup([a(f"{T}/a", ["a-main", "gone"])], commit=commit))
        self.assertMoves(site)
        self.assertEqual((site.blocks, printed),
                         ({}, self.STILL.format(f"{af(1)}: its statements are not published statement pages")))

    def test_an_incomplete_list_of_cards_keeps_the_addresses_and_shows_no_card(self) -> None:
        # The ledger check lists only the cards with an article id no other article has: card 2's id is shared, say.
        def incomplete(made: dict, root: Path) -> dict:
            return {**made, "cards": {af(1): f"{T}/a"}, "cards_complete": False}

        site, printed = self.hook(lambda commit: rollup([card(1, f"{T}/a", ["a-main", "lemma"])], commit=commit),
                                  incomplete)
        self.assertMoves(site)
        self.assertEqual((site.blocks, printed), ({}, self.STILL.format(
            "build/card-moves.json lists only the cards with an article id no other article has, not all of them")))

    def test_a_retired_statement_leads_where_the_receipt_says(self) -> None:
        # The ledger retires the node T/old-note in favour of the lemma, which the receipt places: its old page of its
        # own and its old box both lead there, whatever the card data.
        rows = self.ROWS + ledger({"statement": af(40), "page": f"{T}/old-note", "replaced_by": af(11)})

        def replaced(made: dict, root: Path) -> dict:
            return {**made, "replacements": {**made["replacements"], af(11): {"kind": "page", "node": f"{T}/a/lemma"}}}

        site, printed = self.hook(change=replaced, rows=rows)
        self.assertEqual(printed, self.STILL.format(self.NO_DATA))
        self.assertIn('<p><a href="a/index.html#lemma">Continue to the mathematical page</a></p>',
                      site.files[f"roadmap/{T}/old-note.md"])
        self.assertEqual(RedirectTests.moves(site), {**self.MOVES, f"{T}/old-note": f"{T}/a/lemma"})
        # Without the replacement in the receipt, nothing is kept.
        site, printed = self.hook(rows=rows)
        self.assertIsNone(site)
        self.assertIn(f"::error title=Moved addresses not kept::scripts/card-moves.jsonl: a retired statement's "
                      f"replacements end at {af(11)}, which build/card-moves.json does not list\n", printed)

    def test_a_missing_ledger_is_no_empty_one(self) -> None:
        # A receipt of an empty ledger shows the card data; with the ledger then deleted at the same commit, the hook
        # keeps no moved address and shows no card, as card data needs the moved addresses.
        def full(commit: str) -> dict:
            return rollup([card(1, f"{T}/a", ["a-main", "lemma"]), card(2, f"{T}/b", ["b-main"])], commit=commit)

        site, printed = self.hook(full, rows="")
        self.assertEqual((len(site.blocks), printed), (2, ""))
        site, printed = self.hook(full, lambda made, root: ((root / "scripts/card-moves.jsonl").unlink(), made)[1],
                                  rows="")
        self.assertIsNone(site)
        self.assertEqual(printed, "::warning title=Card data not shown::there is no scripts/card-moves.jsonl\n"
                                  "::error title=Moved addresses not kept::there is no scripts/card-moves.jsonl\n")

    def test_two_moves_of_one_article_into_one_address_keep_nothing_and_say_where(self) -> None:
        # A ledger the check refuses, with a receipt made by hand: lemma (11) moved into a/lemma twice, from two old
        # addresses. The hook keeps no moved address, the unrelated retired card's included, and says why, naming the
        # address; it never takes the second move for the first.
        rows = self.ROWS + ledger({"page": f"{T}/other-lemma", "to": f"{T}/a/lemma", "article_id": af(11)})
        site, printed = self.hook(rows=rows)
        self.assertIsNone(site)
        self.assertIn(f"::error title=Moved addresses not kept::scripts/card-moves.jsonl:3: {af(11)} moves into "
                      f"{T}/a/lemma a second time; an article moves into an address once", printed)
        # The same split between the frozen file and a fragment, and a lawful continuation, which keeps all three.
        site, printed = self.hook(rows=self.ROWS, fragments={"20260101T000000Z-again.jsonl": ledger(
            {"page": f"{T}/other-lemma", "to": f"{T}/a/lemma", "article_id": af(11)})})
        self.assertIsNone(site)
        self.assertIn("scripts/card-moves.d/20260101T000000Z-again.jsonl:1: " + af(11) + " moves into "
                      f"{T}/a/lemma a second time", printed)
        entries = [leaf(f"{T}/a/a-main"), leaf(f"{T}/a/lemma2"), leaf(f"{T}/b/b-main")]
        pages = card_pages.Pages(card_pages.read_index(index(*entries)))
        lawful = card_pages.read_ledger(self.ROWS + ledger(
            {"page": f"{T}/a/lemma", "to": f"{T}/a/lemma2", "article_id": af(11)}))
        self.assertEqual(card_pages.history(lawful, pages, {af(1): ("folder", f"{T}/a")}), {
            ("page", f"{T}/lemma"): f"{T}/a/lemma2", ("page", f"{T}/a/lemma"): f"{T}/a/lemma2",
            ("folder", f"{T}/z"): f"{T}/a"})

    def test_without_this_receipt_no_moved_address_is_kept(self) -> None:
        not_this = "build/card-moves.json is not a receipt of atlas-card-moves/v3"
        for name, change, reason in (
            ("no receipt", lambda made, root: None,
             "there is no build/card-moves.json (the ledger check writes none when the ledger is invalid)"),
            ("not JSON", lambda made, root: "{", "build/card-moves.json is not JSON: "),
            ("another schema", lambda made, root: {**made, "schema": "atlas-card-moves/v0"}, not_this),
            # A v2 receipt digests the frozen file's bytes alone: it says nothing of the fragments.
            ("a v2 receipt", lambda made, root: {**made, "schema": "atlas-card-moves/v2",
                                                 "ledger_sha256": hashlib.sha256(self.ROWS.encode()).hexdigest()},
             not_this),
            ("a key too many", lambda made, root: {**made, "note": ""}, not_this),
            ("a key missing", lambda made, root: {key: value for key, value in made.items() if key != "cards_complete"},
             not_this),
            ("another commit's", lambda made, root: {**made, "commit": COMMIT},
             "build/card-moves.json is not the ledger check of the commit being built"),
            ("another ledger's", lambda made, root: {**made, "ledger_sha256": hashlib.sha256(b"").hexdigest()},
             "build/card-moves.json is the check of another move ledger than the one being built"),
            ("a malformed ledger digest", lambda made, root: {**made, "ledger_sha256": made["ledger_sha256"].upper()},
             "build/card-moves.json is the check of another move ledger than the one being built"),
            ("annotations changed since",
             lambda made, root: ((root / "blueprint/links/A.jsonl").write_bytes(b"\n"), made)[1],
             "build/card-moves.json is the check of other annotations than blueprint/links/ as it is now"),
            ("defaults changed since", lambda made, root: (root / "blueprint/links/_defaults.json").unlink() or made,
             "build/card-moves.json is the check of other annotations than blueprint/links/ as it is now"),
            ("cards that are no table", lambda made, root: {**made, "cards": [af(1)]},
             "build/card-moves.json's cards are not a list of card ids and their folders, one card a folder"),
            ("a card that is no article id", lambda made, root: {**made, "cards": {"af_1": f"{T}/a"}},
             "build/card-moves.json's cards are not a list of card ids and their folders, one card a folder"),
            ("a folder that is no address", lambda made, root: {**made, "cards": {af(1): f"../{T}/a"}},
             "build/card-moves.json's cards are not a list of card ids and their folders, one card a folder"),
            ("two cards in one folder", lambda made, root: {**made, "cards": {af(1): f"{T}/a", af(2): f"{T}/a"}},
             "build/card-moves.json's cards are not a list of card ids and their folders, one card a folder"),
            ("a completeness that is no flag", lambda made, root: {**made, "cards_complete": 1},
             "build/card-moves.json's cards are not a list of card ids and their folders, one card a folder"),
            ("replacements that are no table", lambda made, root: {**made, "replacements": [af(1)]},
             "build/card-moves.json's replacements are not a list of article ids and their pages or folders, one "
             "article an address"),
            ("a replacement of another kind", lambda made, root: {**made, "replacements": {
                af(1): {"kind": "card", "node": f"{T}/a"}}},
             "build/card-moves.json's replacements are not a list of article ids and their pages or folders, one "
             "article an address"),
            ("a replacement with a key too many", lambda made, root: {**made, "replacements": {
                af(1): {"kind": "folder", "node": f"{T}/a", "title": "A"}}},
             "build/card-moves.json's replacements are not a list of article ids and their pages or folders, one "
             "article an address"),
            ("a replacement at no address", lambda made, root: {**made, "replacements": {
                af(1): {"kind": "folder", "node": f"{T}/a.md"}}},
             "build/card-moves.json's replacements are not a list of article ids and their pages or folders, one "
             "article an address"),
            ("two replacements at one address", lambda made, root: {**made, "replacements": {
                af(1): {"kind": "folder", "node": f"{T}/a"}, af(2): {"kind": "folder", "node": f"{T}/a"}}},
             "build/card-moves.json's replacements are not a list of article ids and their pages or folders, one "
             "article an address"),
            ("a replacement it does not list", lambda made, root: {**made, "replacements": {
                af(2): {"kind": "folder", "node": f"{T}/b"}}},
             f"scripts/card-moves.jsonl: a retired card's replacements end at {af(1)}, which build/card-moves.json "
             "does not list"),
            ("a replacement in no published folder", lambda made, root: {**made, "replacements": {
                af(1): {"kind": "folder", "node": f"{T}/gone"}}},
             f"scripts/card-moves.jsonl: a retired card's replacements end at {af(1)}, whose folder {T}/gone the site "
             "does not publish"),
        ):
            with self.subTest(name):
                site, printed = self.hook(change=change)
                self.assertIsNone(site)
                warning, error = printed.splitlines()
                self.assertEqual(warning, f"::warning title=Card data not shown::{self.NO_DATA}")
                self.assertTrue(error.startswith(f"::error title=Moved addresses not kept::{reason}"), error)
        # With card data of this commit too, the hook shows nothing, and says so twice.
        def full(commit: str) -> dict:
            return rollup([card(1, f"{T}/a", ["a-main", "lemma"]), card(2, f"{T}/b", ["b-main"])], commit=commit)

        site, printed = self.hook(full, lambda made, root: None)
        self.assertIsNone(site)
        self.assertEqual(printed.count("there is no build/card-moves.json"), 2)


class ResolverOrderTests(unittest.TestCase):
    """The reverse replay (history) judges what a row says against a fallback at the historical point: a folder row or
    a card's retirement replaces the fallback of a gone folder that a later row's replay put in place, whatever the
    order of the two in the ledger; a fallback never replaces what a row said. These are tests of the resolver alone,
    in both orders, apart from the fragment guard that declines the pair as two new fragments (scripts/test_cards.py,
    Fragments)."""

    ENTRIES = [leaf(f"{T}/live/u"), leaf(f"{T}/live/w"), folder(f"{T}/live"), folder(T), folder("A/f"), folder("A"),
               folder("roadmap")]

    def history(self, *rows: dict, replacements: dict | None = None) -> dict:
        pages = card_pages.Pages(card_pages.read_index(index(*self.ENTRIES)))
        return card_pages.history(card_pages.read_ledger(ledger(*rows)), pages,
                                  replacements or {af(1): ("folder", f"{T}/live")})

    def test_a_move_out_of_a_folder_and_its_card_s_retirement_resolve_alike_in_both_orders(self) -> None:
        # P: the statement 11 moves out of T/old into T/live; R: card 7 is retired at T/old, replaced by card 1 at
        # T/live. Before the fix, R then P led T/old to T, the fallback P's replay put there first.
        p = {"page": f"{T}/old/u", "to": f"{T}/live/u", "article_id": af(11)}
        r = {"card": af(7), "folder": f"{T}/old", "replaced_by": af(1)}
        expected = {("page", f"{T}/old/u"): f"{T}/live/u", ("folder", f"{T}/old"): f"{T}/live"}
        self.assertEqual(self.history(p, r), expected)
        self.assertEqual(self.history(r, p), expected)

    def test_a_fallback_taken_from_above_an_overridden_folder_is_taken_from_it(self) -> None:
        # The statement left T/old/sub, a folder in T/old that is gone too; T/old's retirement says where T/old leads,
        # and T/old/sub, nearer to it than T, leads there as well, in both orders.
        p = {"page": f"{T}/old/sub/u", "to": f"{T}/live/u", "article_id": af(11)}
        r = {"card": af(7), "folder": f"{T}/old", "replaced_by": af(1)}
        expected = {("page", f"{T}/old/sub/u"): f"{T}/live/u", ("folder", f"{T}/old"): f"{T}/live",
                    ("folder", f"{T}/old/sub"): f"{T}/live"}
        self.assertEqual(self.history(p, r), expected)
        self.assertEqual(self.history(r, p), expected)

    def test_a_folder_row_beats_a_fallback_and_never_the_reverse(self) -> None:
        # The folder T/old became T/live; a statement left it before or after. Its old address leads where the row
        # says, not to T, in both orders; the folder's own row moves it alone.
        folder_row = {"folder": f"{T}/old", "to": f"{T}/live", "article_id": af(50)}
        page_row = {"page": f"{T}/old/w", "to": f"{T}/live/w", "article_id": af(12)}
        expected = {("folder", f"{T}/old"): f"{T}/live", ("page", f"{T}/old/w"): f"{T}/live/w"}
        self.assertEqual(self.history(folder_row, page_row), expected)
        self.assertEqual(self.history(page_row, folder_row), expected)

    def test_fallbacks_resting_on_fallbacks_follow_the_retirement_at_any_depth(self) -> None:
        # a moves into old/sub/deep and out; b leaves old/sub, c leaves old; card 7 at old is retired for card 1. The
        # replay infers old, then old/sub from old, then old/sub/deep from old/sub, in one order of the sibling moves,
        # or old and old/sub from T in the other: either way the retirement of old reaches all three.
        entries = [leaf(f"{T}/live/a"), leaf(f"{T}/live/b"), leaf(f"{T}/live/c"), folder(f"{T}/live")]
        enter = {"page": f"{T}/old/a", "to": f"{T}/old/sub/deep/a", "article_id": af(11)}
        retire = {"card": af(7), "folder": f"{T}/old", "replaced_by": af(1)}
        leave = {"page": f"{T}/old/sub/deep/a", "to": f"{T}/live/a", "article_id": af(11)}
        sub = {"page": f"{T}/old/sub/b", "to": f"{T}/live/b", "article_id": af(12)}
        old = {"page": f"{T}/old/c", "to": f"{T}/live/c", "article_id": af(13)}
        expected = {("folder", f"{T}/old"): f"{T}/live", ("folder", f"{T}/old/sub"): f"{T}/live",
                    ("folder", f"{T}/old/sub/deep"): f"{T}/live", ("page", f"{T}/old/a"): f"{T}/live/a",
                    ("page", f"{T}/old/sub/deep/a"): f"{T}/live/a", ("page", f"{T}/old/sub/b"): f"{T}/live/b",
                    ("page", f"{T}/old/c"): f"{T}/live/c"}
        pages = card_pages.Pages(card_pages.read_index(index(*entries)))
        for rows in ((enter, retire, leave, sub, old), (enter, retire, leave, old, sub),
                     (retire, enter, old, leave, sub)):
            with self.subTest(rows=[next(iter(row.values())) for row in rows]):
                self.assertEqual(card_pages.history(card_pages.read_ledger(ledger(*rows)), pages,
                                                    {af(1): ("folder", f"{T}/live")}), expected)

    def test_a_card_replaced_in_place_keeps_its_chain(self) -> None:
        # Card 7 was retired at T/live for card 8, in place, which was retired there for card 1, in place too: the
        # folder is live, so no fallback and no explicit row moves it.
        rows = ({"card": af(7), "folder": f"{T}/live", "replaced_by": af(8)},
                {"card": af(8), "folder": f"{T}/live", "replaced_by": af(1)})
        self.assertEqual(self.history(*rows), {})
        # Gone, the folder leads to the last replacement's.
        rows = ({"card": af(7), "folder": f"{T}/gone", "replaced_by": af(8)},
                {"card": af(8), "folder": f"{T}/gone", "replaced_by": af(1)})
        self.assertEqual(self.history(*rows), {("folder", f"{T}/gone"): f"{T}/live"})


class OracleTests(unittest.TestCase):
    """The site's redirects against a hand-written oracle: for each history below, written forward as it happened,
    the final endpoint of every old address and every route the site emits for it, set down independently of the
    reverse resolver. Equal permutations can agree on a wrong endpoint; this cannot."""

    def emitted(self, entries, cards, rows, replacements=None) -> dict:
        with tempfile.TemporaryDirectory() as docs:
            site = card_pages.build(rollup(cards), index(*entries), rows, Path(docs), replacements=replacements)
        notices = {}
        for path, text in site.files.items():
            if path.endswith(".md") and path.startswith("roadmap/"):
                target = text.split('<p><a href="', 1)[1].split('"', 1)[0]
                notices[path] = (target, "http-equiv" in text,
                                 sorted(RedirectTests.elements(text)))
        return {"notices": notices,
                "anchors": {page: sorted((slug, RedirectTests.elements(element)[0][1]) for slug, element in pairs)
                            for page, pairs in site.anchors.items()},
                "table": RedirectTests.moves(site) if card_pages.SCRIPT in site.files else {},
                "explorer": sorted(path for path in site.files if path.startswith("dependencies/scopes/"))}

    def test_a_folder_renamed_with_its_statements_then_a_card_retired_into_it(self) -> None:
        # Forward: the folder T/old (1), with its statements a (10) and b (11), became the card folder T/card; then
        # card 7 at T/z, which held z (12), was dissolved: z moved into T/card, and card 7 was retired for card 1.
        entries = [leaf(f"{T}/card/a"), leaf(f"{T}/card/b", own_page=True), leaf(f"{T}/card/z"),
                   folder(f"{T}/card")]
        rows = [*rename(f"{T}/old", f"{T}/card", 1, pages={"a": 10, "b": 11}),
                {"page": f"{T}/z/z", "to": f"{T}/card/z", "article_id": af(12)},
                {"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)}]
        found = self.emitted(entries, [card(1, f"{T}/card", ["a", "b", "z"])], ledger(*rows))
        self.assertEqual(found, {
            "notices": {
                # Every old page route: a boxed statement's anchor on its folder page, a statement of its own page.
                f"roadmap/{T}/old/a.md": ("../card/index.html#a", True, []),
                f"roadmap/{T}/old/b.md": ("../card/b.html", True, []),
                f"roadmap/{T}/z/z.md": ("../card/index.html#z", True, []),
                # Every gone folder: its notice, with an element for each old anchor, and no refresh.
                f"roadmap/{T}/old/README.md": ("../card/index.html", False,
                                               [("a", "../card/index.html#a"), ("b", "../card/b.html")]),
                f"roadmap/{T}/z/README.md": ("../card/index.html", False, [("z", "../card/index.html#z")])},
            "anchors": {},
            "table": {f"{T}/old": f"{T}/card", f"{T}/old/a": f"{T}/card/a", f"{T}/old/b": f"{T}/card/b",
                      f"{T}/z": f"{T}/card", f"{T}/z/z": f"{T}/card/z"},
            "explorer": [f"dependencies/scopes/{T}/old.md", f"dependencies/scopes/{T}/z.md"]})

    def test_statements_retired_into_a_page_a_folder_and_in_place(self) -> None:
        # Forward: the node T/n (20) was expanded into the folder T/n of its own name (21); the node T/m (22) was
        # retired for T/j (24), which was then retired for the page T/k (23); and the boxed node T/i (25) was retired
        # for T/h (26), which then moved into T/i, in place.
        entries = [leaf(f"{T}/k", own_page=True), leaf(f"{T}/i"), leaf(f"{T}/n/part"), folder(f"{T}/n"), folder(T)]
        rows = [{"statement": af(20), "page": f"{T}/n", "replaced_by": af(21)},
                {"statement": af(22), "page": f"{T}/m", "replaced_by": af(24)},
                {"statement": af(24), "page": f"{T}/j", "replaced_by": af(23)},
                {"statement": af(25), "page": f"{T}/i", "replaced_by": af(26)},
                {"page": f"{T}/h", "to": f"{T}/i", "article_id": af(26)}]
        replacements = {af(21): ("folder", f"{T}/n"), af(23): ("page", f"{T}/k"), af(26): ("page", f"{T}/i")}
        found = self.emitted(entries, [], ledger(*rows), replacements)
        self.assertEqual(found, {
            "notices": {
                # The node expanded into the folder of its name: its old page of its own leads to the folder.
                f"roadmap/{T}/n.md": ("n/index.html", True, []),
                # A chain of retirements ends at the live page k, from both of its addresses.
                f"roadmap/{T}/m.md": ("k.html", True, []), f"roadmap/{T}/j.md": ("k.html", True, []),
                # h moved, then sits at i, in place of the boxed i: h's old page leads to i's box, and i's own old
                # page of its own (the route the boxed replacement lacks) too.
                f"roadmap/{T}/h.md": ("index.html#i", True, []), f"roadmap/{T}/i.md": ("index.html#i", True, [])},
            # On T's page, each old box the endpoint does not have itself: n's, m's, j's, h's (whose link, on the page
            # of i's box, is the box's own anchor); never i's.
            "anchors": {f"roadmap/{T}/index.html": [("h", "#i"), ("j", "k.html"), ("m", "k.html"),
                                                     ("n", "n/index.html")]},
            # An explorer link to an address that leads to itself needs no rewrite.
            "table": {f"{T}/h": f"{T}/i", f"{T}/j": f"{T}/k", f"{T}/m": f"{T}/k"},
            "explorer": []})


class LedgerDigestTests(unittest.TestCase):
    """The receipt's ledger digest (docs/cards.md#reading): per file, in logical order, its path, a NUL, its length
    in decimal, a NUL and its bytes; never a join of the rows."""

    FILES = [("scripts/card-moves.jsonl", b'{"a": "1"}\n'), ("scripts/card-moves.d/20260101T000000Z-x.jsonl",
                                                             b'{"b": "2"}\n{"c": "3"}\n')]

    def test_the_digest_frames_each_file(self) -> None:
        framed = b"".join(path.encode() + b"\0" + str(len(data)).encode() + b"\0" + data for path, data in self.FILES)
        self.assertEqual(card_pages.ledger_digest(self.FILES), hashlib.sha256(framed).hexdigest())
        self.assertEqual(card_pages.ledger_digest(self.FILES), ledger_digest(self.FILES))
        self.assertNotEqual(card_pages.ledger_digest(self.FILES),
                            hashlib.sha256(b"".join(data for _, data in self.FILES)).hexdigest())

    def test_a_name_or_a_part_boundary_changes_the_digest(self) -> None:
        renamed = [self.FILES[0], ("scripts/card-moves.d/20260101T000000Z-y.jsonl", self.FILES[1][1])]
        moved = [("scripts/card-moves.jsonl", b'{"a": "1"}\n{"b": "2"}\n'),
                 ("scripts/card-moves.d/20260101T000000Z-x.jsonl", b'{"c": "3"}\n')]
        digests = {card_pages.ledger_digest(files) for files in (self.FILES, renamed, moved)}
        self.assertEqual(len(digests), 3)


class FragmentReceiptTests(unittest.TestCase):
    """The hook reads the ledger's frozen file and its fragments (ledger_files) and keeps the moved addresses only with
    an `atlas-card-moves/v3` receipt of those very files: stale, missing, malformed and non-regular parts each keep
    nothing."""

    hook = ReceiptTests.hook
    assertMoves = ReceiptTests.assertMoves
    ENTRIES, ROWS, CARDS, LINKS, MOVES, NO_DATA = (ReceiptTests.ENTRIES, ReceiptTests.ROWS, ReceiptTests.CARDS,
                                                    ReceiptTests.LINKS, ReceiptTests.MOVES, ReceiptTests.NO_DATA)
    STILL = ReceiptTests.STILL
    PART = "scripts/card-moves.d/20260101T000000Z-z.jsonl"

    def split(self, change=None):
        rows = self.ROWS.splitlines(keepends=True)
        return self.hook(change=change, rows=rows[0], fragments={self.PART.rsplit("/", 1)[1]: rows[1]})

    def test_a_ledger_split_into_fragments_keeps_its_addresses(self) -> None:
        site, printed = self.split()
        self.assertMoves(site)
        self.assertEqual(printed, self.STILL.format(self.NO_DATA))

    def test_a_part_changed_after_the_receipt_keeps_nothing(self) -> None:
        late = ledger({"page": f"{T}/elsewhere", "to": f"{T}/b/b-main", "article_id": af(13)})
        another = "build/card-moves.json is the check of another move ledger than the one being built"
        for name, change, reason in (
            ("a fragment added", lambda made, root: (
                (root / "scripts/card-moves.d/20260102T000000Z-late.jsonl").write_text(late), made)[1], another),
            ("a fragment deleted", lambda made, root: ((root / self.PART).unlink(), made)[1], another),
            ("a fragment renamed", lambda made, root: (
                (root / self.PART).rename(root / self.PART.replace("-z.", "-y.")), made)[1], another),
            ("a fragment edited", lambda made, root: ((root / self.PART).write_text(
                (root / self.PART).read_text() + "\n"), made)[1], another),
            ("rows moved across the boundary", lambda made, root: (
                (root / "scripts/card-moves.jsonl").write_text(self.ROWS), (root / self.PART).write_text(
                    "\n" + self.ROWS.splitlines(keepends=True)[1]), made)[2], another),
            ("an entry that is no fragment", lambda made, root: (
                (root / "scripts/card-moves.d/notes.txt").write_text("x\n"), made)[1],
             "scripts/card-moves.d/notes.txt: not a fragment"),
            ("a fragment that is a link", lambda made, root: (
                (root / "kept.jsonl").write_bytes((root / self.PART).read_bytes()), (root / self.PART).unlink(),
                (root / self.PART).symlink_to(root / "kept.jsonl"), made)[3], f"{self.PART}: no regular file"),
            ("a folder that is no folder", lambda made, root: (
                shutil.rmtree(root / "scripts/card-moves.d"), (root / "scripts/card-moves.d").write_text(""), made)[2],
             "scripts/card-moves.d is no folder"),
            ("a folder that is a link to the same fragments elsewhere", lambda made, root: (
                (root / "scripts/card-moves.d").rename(root / "kept"),
                (root / "scripts/card-moves.d").symlink_to(root / "kept"), made)[2],
             "scripts/card-moves.d is no folder"),
            ("a frozen file that is gone", lambda made, root: ((root / "scripts/card-moves.jsonl").unlink(), made)[1],
             "there is no scripts/card-moves.jsonl"),
        ):
            with self.subTest(name):
                site, printed = self.split(change)
                self.assertIsNone(site)
                self.assertIn(f"::error title=Moved addresses not kept::{reason}", printed)


class ReportTests(unittest.TestCase):
    """What the site does not show, the build says: at INFO in its log, since `mkdocs build --strict` fails on a
    warning, and under GitHub Actions as a workflow annotation and a line of the job summary."""

    def report(self, environment: dict[str, str]) -> tuple[list[str], str]:
        printed = io.StringIO()
        with mock.patch.dict(os.environ, environment), contextlib.redirect_stdout(printed), \
                self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged:
            card_pages.report("error", "Moved addresses not kept", "100% <gone>:\r\nnext, line",
                              said="Moved addresses NOT kept")
        self.assertEqual([record.levelname for record in logged.records], ["INFO"])
        return logged.output, printed.getvalue()

    def test_a_report_under_github_actions(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            summary = Path(temporary) / "summary.md"
            summary.write_text("Before.\n", encoding="utf-8")
            logged, printed = self.report({"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(summary)})
            self.assertEqual(summary.read_text(encoding="utf-8"),
                             "Before.\n- **Moved addresses not kept**: 100% &lt;gone&gt;: next, line\n")
        self.assertEqual(logged, ["INFO:mkdocs.hooks.card_pages:Moved addresses NOT kept: 100% <gone>:\r\nnext, line"])
        # One workflow command: `%`, CR and LF escaped in its message, and `:` and `,` in a property too.
        self.assertEqual(printed, "::error title=Moved addresses not kept::100%25 <gone>:%0D%0Anext, line\n")
        self.assertEqual(card_pages.workflow_text("a: b, c", True), "a%3A b%2C c")

    def test_a_report_elsewhere_is_a_log_line_alone(self) -> None:
        with mock.patch.dict(os.environ):
            os.environ.pop("GITHUB_ACTIONS", None)
            logged, printed = self.report({"GITHUB_STEP_SUMMARY": ""})
        self.assertEqual((len(logged), printed), (1, ""))


@unittest.skipIf(shutil.which("node") is None, "needs Node.js to run the explorer's rewrite")
class ExplorerLinkTests(unittest.TestCase):
    """An old explorer link `#node=<address>` is rewritten to where the address leads, before the explorer starts."""

    @classmethod
    def setUpClass(cls) -> None:
        # The script the site serves for a history with every kind of row: a statement that leaves a folder between
        # two renames, a child folder that leaves a renamed folder, a card that merges into another, and a page
        # added to the renamed folder afterwards, with no row.
        with tempfile.TemporaryDirectory() as docs:
            site = card_pages.build(
                rollup([card(1, f"{T}/c", ["c-main", "z-main"]), card(2, f"{T}/elsewhere", ["y"])]),
                index(leaf(f"{T}/new/kept"), leaf(f"{T}/new/fresh"), leaf(f"{T}/c/c-main"), leaf(f"{T}/c/z-main"),
                      leaf(f"{T}/elsewhere/y"), leaf("A/g/sub/s")),
                ledger(*rename(f"{T}/old", f"{T}/mid", 50, pages={"kept": 11, "x": 10}, folders={"sub": 60}),
                       {"page": f"{T}/old/sub/s", "to": f"{T}/mid/sub/s", "article_id": af(12)},
                       {"page": f"{T}/mid/x", "to": f"{T}/elsewhere/y", "article_id": af(10)},
                       *rename(f"{T}/mid", f"{T}/new", 50, pages={"kept": 11}, folders={"sub": 60}),
                       {"page": f"{T}/mid/sub/s", "to": f"{T}/new/sub/s", "article_id": af(12)},
                       *rename(f"{T}/new/sub", "A/g/sub", 60, pages={"s": 12}),
                       {"page": f"{T}/z/z-main", "to": f"{T}/c/z-main", "article_id": af(31)},
                       {"card": af(7), "folder": f"{T}/z", "replaced_by": af(1)}), Path(docs))
        cls.script = site.files[card_pages.SCRIPT]

    def rewrite(self, hash_: str) -> str | None:
        script = self.script
        harness = ("globalThis.location = {hash: process.argv[1]}; var written = null;\n"
                   "globalThis.history = {state: {kept: 1}, replaceState: function (state, title, url) {\n"
                   "  if (state.kept !== 1 || title !== '') throw new Error('state'); written = url; }};\n"
                   f"{script}\nconsole.log(JSON.stringify(written));")
        result = subprocess.run(["node", "-e", harness, hash_], capture_output=True, text=True, check=True)
        return json.loads(result.stdout)

    def test_old_addresses_are_rewritten(self) -> None:
        node = "#node=" + T.replace("/", "%2F")
        # A statement that left a folder between two renames: from both its old addresses, never to new/x.
        self.assertEqual(self.rewrite(f"#node={T}/old/x"), f"{node}%2Felsewhere%2Fy")
        self.assertEqual(self.rewrite(f"{node}%2Fmid%2Fx"), f"{node}%2Felsewhere%2Fy")
        self.assertEqual(self.rewrite(f"#node={T}/old"), f"{node}%2Fnew")
        self.assertEqual(self.rewrite(f"#node={T}/old/kept"), f"{node}%2Fnew%2Fkept")
        # A child folder that left the renamed folder, from its address before the rename and after.
        self.assertEqual(self.rewrite(f"#node={T}/old/sub/s"), "#node=A%2Fg%2Fsub%2Fs")
        self.assertEqual(self.rewrite(f"#node={T}/new/sub"), "#node=A%2Fg%2Fsub")
        # A card merged into another.
        self.assertEqual(self.rewrite(f"#node={T}/z/z-main"), f"{node}%2Fc%2Fz-main")
        # The explorer's scope and boundary selections keep their kind, and its other parameters stay.
        self.assertEqual(self.rewrite(f"#view=graph&node=scope%3A{T}%2Fz"), f"#view=graph&node=scope%3A{T[0]}%2F"
                         f"{T.split('/')[1]}%2F{T.split('/')[2]}%2Fc")

    def test_other_links_are_left_alone(self) -> None:
        for hash_ in ("", "#x-main", f"#node={T}/c/c-main", f"#node={T}/new/x", f"#node={T}/old/fresh",
                      f"#node={T}/mid/fresh", f"#node={T}/oldish", "#view=list"):
            with self.subTest(hash_):
                self.assertIsNone(self.rewrite(hash_))


class SiteBuildTests(unittest.TestCase):
    """Build a small site with the repository's configuration, theme and hooks: without card data of the commit
    being built, the site is byte for byte the site without the card hook but for the moved addresses, which it keeps
    with the ledger check's receipt, and the build says why it shows no card."""

    PAGES = {
        "index.md": "# Home\n",
        "roadmap/README.md": "# ATLAS roadmap\n\n- [Subject A](A/README.md)\n",
        "roadmap/A/README.md": "# Subject A\n\n- [Field F](f/README.md)\n",
        "roadmap/A/f/README.md": "# Field F\n\n- [Topic T](t/README.md)\n",
    }
    READING = ('<div class="bp-explorer-page" markdown="1">\n'
               '<div class="bp-reading-source" data-autoform-node-id="{id}" markdown="1">\n\n{body}\n</div>\n</div>\n')
    SUMMARY = ("- [Home](index.md)\n- [ATLAS roadmap](roadmap/README.md)\n    - [Subject A](roadmap/A/README.md)\n"
               "        - [Field F](roadmap/A/f/README.md)\n            - [Topic T](roadmap/A/f/t/README.md)\n"
               "                - [Card C](roadmap/A/f/t/c/README.md)\n")

    @classmethod
    def setUpClass(cls) -> None:
        logging.getLogger("mkdocs").setLevel(logging.ERROR)
        # The hook reports to GitHub Actions, where these tests run too: only a test that asks for its reports gets
        # them.
        environment = mock.patch.dict(os.environ)
        environment.start()
        cls.addClassCleanup(environment.stop)
        for name in ("GITHUB_ACTIONS", "GITHUB_STEP_SUMMARY"):
            os.environ.pop(name, None)
        temporary = tempfile.TemporaryDirectory(prefix="atlas-card-pages-")
        cls.addClassCleanup(temporary.cleanup)
        cls.root = Path(temporary.name)
        for name in ("hooks", "theme"):
            (cls.root / name).symlink_to(ROOT / name)
        docs = cls.root / "site-src"
        pages = {
            **cls.PAGES,
            "roadmap/A/f/t/README.md": cls.READING.format(id=T, body="# Topic T\n\n- [Card C](c/README.md)\n"),
            "roadmap/A/f/t/c/README.md": cls.READING.format(id=f"{T}/c", body=(
                "# Card C\n\nThe main statement in words.\n\n## Idea\n\nWhy it matters.\n\n## Statements\n\n"
                '<div class="bp-thmwrapper" data-autoform-node-id="A/f/t/c/main" markdown="1">\n'
                '<h4 class="bp-thmheading" id="main">Main</h4>\n</div>\n')),
            "SUMMARY.md": cls.SUMMARY,
            "dependencies/index.json": json.dumps(index(leaf(f"{T}/c/main", "Main"), folder(f"{T}/c", "Card C"))),
        }
        for path, text in pages.items():
            (docs / path).parent.mkdir(parents=True, exist_ok=True)
            (docs / path).write_text(text, encoding="utf-8")
        (cls.root / "scripts").mkdir()
        git = ["git", "-C", str(cls.root), "-c", "user.name=Test", "-c", "user.email=test@example.com"]
        subprocess.run([*git, "init", "-q"], check=True)
        subprocess.run([*git, "commit", "-q", "--allow-empty", "-m", "fixture"], check=True)
        cls.commit = subprocess.run([*git, "rev-parse", "HEAD"], check=True, capture_output=True,
                                    text=True).stdout.strip()
        configuration = (ROOT / "mkdocs.yml").read_text(encoding="utf-8")
        hook = "  - hooks/card_pages.py\n"
        assert hook in configuration
        (cls.root / "mkdocs.yml").write_text(configuration, encoding="utf-8")
        (cls.root / "without-cards.yml").write_text(configuration.replace(hook, ""), encoding="utf-8")
        cls.baseline = cls.build("without-cards.yml", None)

    LEDGER = ledger({"page": f"{T}/main", "to": f"{T}/c/main", "article_id": af(10)})
    # The cards the ledger check lists: card 1, whose folder is the card page.
    CARDS = {af(1): f"{T}/c"}

    @classmethod
    def build(cls, configuration: str, data: dict | str | None, rows: str = LEDGER, cards: dict | None = CARDS
              ) -> dict[str, bytes]:
        """The site built with the card data ``data``, the ledger ``rows`` and the receipt of the ledger check, which
        lists ``cards`` (None: no receipt)."""
        from mkdocs.commands.build import build
        from mkdocs.config import load_config

        (cls.root / "scripts" / "card-moves.jsonl").write_text(rows, encoding="utf-8")
        (cls.root / "build").mkdir(exist_ok=True)
        moves = cls.root / "build" / "card-moves.json"
        moves.unlink(missing_ok=True)
        if cards is not None:
            moves.write_text(json.dumps(receipt(cls.commit, rows, cards)), encoding="utf-8")
        data_file = cls.root / "build" / "cards.json"
        data_file.unlink(missing_ok=True)
        if data is not None:
            data_file.write_text(data if isinstance(data, str) else json.dumps(data), encoding="utf-8")
        site = cls.root / "site"
        shutil.rmtree(site, ignore_errors=True)
        build(load_config(str(cls.root / configuration), site_dir=str(site)))
        return {path.relative_to(site).as_posix(): path.read_bytes() for path in sorted(site.rglob("*"))
                if path.is_file()}

    def data(self, commit: str | None = None) -> dict:
        return rollup([card(1, f"{T}/c", ["main"])], commit=commit or self.commit)

    def assertSameSite(self, site: dict[str, bytes], expected: dict[str, bytes]) -> None:
        self.assertEqual(sorted(site), sorted(expected))
        self.assertEqual([path for path in site if site[path] != expected[path]], [])

    @contextlib.contextmanager
    def github(self):
        """As under GitHub Actions: what the hook prints, and the job summary it writes to."""
        summary = self.root / "summary.md"
        summary.unlink(missing_ok=True)
        printed = io.StringIO()
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(summary)}), \
                contextlib.redirect_stdout(printed):
            yield printed, summary

    def bad(self) -> dict:
        """Card data of this commit with a card error: a statement the site does not publish."""
        bad = self.data()
        bad["cards"][0]["pages"] = [f"{T}/c/main", f"{T}/c/unpublished"]
        return bad

    def test_without_card_data_of_this_commit_only_the_moved_addresses_are_kept(self) -> None:
        # The site of card data with no card, on a commit with no card, and the same ledger; with no moved address,
        # the site without the hook.
        moved = self.build("mkdocs.yml", rollup([], commit=self.commit), cards={})
        self.assertIn("javascripts/atlas-card-moves.js", moved)
        for name, data in (("no card data", None), ("another commit's", self.data(COMMIT)), ("not JSON", "{"),
                           ("a bad card", self.bad()), ("another schema", {**self.data(), "schema": "atlas-cards/v0"})):
            with self.subTest(name):
                self.assertSameSite(self.build("mkdocs.yml", data), moved)
                self.assertSameSite(self.build("mkdocs.yml", data, ""), self.baseline)

    def test_a_card_error_on_main_keeps_every_moved_address_and_says_so(self) -> None:
        # A card error on main, which the merge queue does not stop, leaves no card data or card data the hook
        # refuses: the site shows no card, but every address of the ledger still leads to its page, and the build
        # says why there is no card.
        for name, data, reason in (
                ("no card data", None, f"there is no {card_pages.DATA} (the rollup writes none when the strict check "
                                       "fails)"),
                ("a bad card", self.bad(), f"{af(1)}: its statements are not published statement pages")):
            with self.subTest(name), self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged, \
                    self.github() as (printed, summary):
                site = self.build("mkdocs.yml", data)
            topic = site[f"roadmap/{T}/index.html"].decode()
            # On the old folder page: the old anchor with its plain link, and the stylesheet that styles it.
            self.assertIn('<p class="atlas-moved" id="main">This statement moved: <a href="c/index.html#main">Main'
                          "</a>.</p>", topic)
            self.assertIn('<link rel="stylesheet" href="../../../../stylesheets/atlas-cards.css">', topic)
            # The explorer's rewrite, which the pages an old explorer link reaches load first.
            self.assertIn('<script src="../../../../javascripts/atlas-card-moves.js"></script></head>', topic)
            self.assertIn("javascripts/atlas-card-moves.js", site)
            # The notice at the statement's old page of its own.
            self.assertIn('<p><a href="c/index.html#main">Continue to the mathematical page</a></p>',
                          site[f"roadmap/{T}/main.html"].decode())
            # No card block.
            self.assertNotIn("atlas-card\"", site[f"roadmap/{T}/c/index.html"].decode())
            # Said at INFO, as a warning would fail `mkdocs build --strict`, and to GitHub Actions.
            said = f"{reason}; moved addresses are still kept"
            self.assertIn(f"INFO:mkdocs.hooks.card_pages:Card data not shown: {said}", logged.output)
            self.assertEqual({record.levelname for record in logged.records}, {"INFO"})
            self.assertEqual(printed.getvalue(), f"::warning title=Card data not shown::{said}\n")
            self.assertEqual(summary.read_text(encoding="utf-8"), f"- **Card data not shown**: {said}\n")

    def test_without_the_ledger_checks_receipt_nothing_is_kept_and_it_says_so(self) -> None:
        # The ledger check wrote no receipt (the ledger is invalid), with or without card data: nothing is added.
        reason = "there is no build/card-moves.json (the ledger check writes none when the ledger is invalid)"
        for name, data in (("no card data", None), ("card data of this commit", self.data())):
            with self.subTest(name), self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged, \
                    self.github() as (printed, summary):
                self.assertSameSite(self.build("mkdocs.yml", data, cards=None), self.baseline)
            self.assertIn(f"INFO:mkdocs.hooks.card_pages:Moved addresses NOT kept: {reason}", logged.output)
            self.assertEqual({record.levelname for record in logged.records}, {"INFO"})
            self.assertIn(f"::error title=Moved addresses not kept::{reason}\n", printed.getvalue())
            self.assertIn(f"- **Moved addresses not kept**: {reason}\n", summary.read_text(encoding="utf-8"))
            self.assertIn("::warning title=Card data not shown::", printed.getvalue())
            self.assertNotIn("still kept", "\n".join(logged.output))

    def test_a_ledger_that_leads_nowhere_the_site_publishes_keeps_nothing_and_says_so(self) -> None:
        rows = ledger({"page": f"{T}/main", "to": f"{T}/c/gone", "article_id": af(10)})
        reason = f"scripts/card-moves.jsonl: the page {T}/main leads to {T}/c/gone, which is no published statement"
        for name, data in (("no card data", None), ("card data of this commit", self.data())):
            with self.subTest(name), self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged, \
                    self.github() as (printed, summary):
                self.assertSameSite(self.build("mkdocs.yml", data, rows), self.baseline)
            self.assertIn(f"INFO:mkdocs.hooks.card_pages:Moved addresses NOT kept: {reason}", logged.output)
            self.assertIn(f"::error title=Moved addresses not kept::{reason}\n", printed.getvalue())
            self.assertIn(f"- **Moved addresses not kept**: {reason}\n", summary.read_text(encoding="utf-8"))
            # Card data needs the moved addresses too: none is shown, and nothing says that they are kept.
            self.assertIn("::warning title=Card data not shown::", printed.getvalue())
            self.assertNotIn("still kept", "\n".join(logged.output))

    def test_a_rollup_with_nothing_to_show_changes_nothing(self) -> None:
        # Before any card merges, the rollup of the commit passes with no card, and the ledger is empty.
        with self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged:
            self.assertEqual(self.build("mkdocs.yml", rollup([], commit=self.commit), "", cards={}), self.baseline)
        self.assertIn("Card data with no card and no moved address", "\n".join(logged.output))

    def test_moved_addresses_are_kept_with_no_card(self) -> None:
        site = self.build("mkdocs.yml", rollup([], commit=self.commit), cards={})
        topic = site[f"roadmap/{T}/index.html"].decode()
        self.assertIn('<p class="atlas-moved" id="main">', topic)
        self.assertIn('href="../../../../stylesheets/atlas-cards.css"', topic)
        self.assertNotIn("atlas-card\"", site[f"roadmap/{T}/c/index.html"].decode())

    def test_an_old_explorer_bookmark_through_a_page_only_folder_is_rewritten_in_the_built_site(self) -> None:
        # The only row moves the page p/x out of p, whose folder page stays with nothing below it, indexed as a node at
        # its own page. In the built site, the bookmark dependencies/scopes/A/f/t/p.html#node=A/f/t/p/x runs its
        # notice's script to p's own page with the fragment, and p's page loads the rewrite table, which selects
        # where x went: the alias's script, then the table, run as the browser runs them.
        docs = self.root / "site-src"
        source, index_file = docs / f"roadmap/{T}/p/README.md", docs / "dependencies/index.json"
        saved = index_file.read_text(encoding="utf-8")
        source.parent.mkdir(parents=True)
        self.addCleanup(shutil.rmtree, source.parent)
        self.addCleanup(index_file.write_text, saved, encoding="utf-8")
        source.write_text(self.READING.format(id=f"{T}/p", body="# Page-only P\n"), encoding="utf-8")
        nodes = json.loads(saved)
        nodes["nodes"].append(node_folder(f"{T}/p", "Page-only P"))
        index_file.write_text(json.dumps(nodes), encoding="utf-8")
        site = self.build("mkdocs.yml", None, ledger({"page": f"{T}/p/x", "to": f"{T}/c/main", "article_id": af(10)}),
                          cards={})
        page = site[f"roadmap/{T}/p/index.html"].decode()
        self.assertIn("Page-only P", page)
        self.assertNotIn('class="bp-moved"', page)
        self.assertIn('<script src="../../../../../javascripts/atlas-card-moves.js"></script></head>', page)
        alias = site[f"dependencies/scopes/{T}/p.html"].decode()
        script = next(part for part in alias.split("<script>")[1:] if "location.replace(" in part).split("</script>")[0]
        harness = (
            "const vm = require('node:vm'), start = new URL(process.argv[1]); let landing;\n"
            "vm.runInNewContext(process.argv[2], {URL, decodeURIComponent, document: {getElementById: () => null},\n"
            "  location: {href: start.href, hash: start.hash,\n"
            "             replace: (to) => { landing = new URL(to, start.href); }}});\n"
            "vm.runInNewContext(process.argv[3], {URLSearchParams, location: landing, history: {state: null,\n"
            "  replaceState: (state, title, to) => { landing = new URL(to, landing); }}});\n"
            "console.log(JSON.stringify([landing.pathname, new URLSearchParams(landing.hash.slice(1)).get('node')]));")
        start = f"https://example.invalid/site/dependencies/scopes/{T}/p.html#node={T}/p/x"
        table = site["javascripts/atlas-card-moves.js"].decode()
        result = subprocess.run(["node", "-e", harness, start, script, table], capture_output=True, text=True,
                                check=True)
        self.assertEqual(json.loads(result.stdout), [f"/site/roadmap/{T}/p/index.html", f"{T}/c/main"])

    def test_card_data_of_this_commit_is_shown(self) -> None:
        site = self.build("mkdocs.yml", self.data())
        self.assertNotEqual(site, self.baseline)
        card_page = site[f"roadmap/{T}/c/index.html"].decode()
        block = card_page.index('<div class="atlas-card">')
        self.assertLess(card_page.index("The main statement in words."), block)
        self.assertLess(block, card_page.index('id="idea"'))
        self.assertIn('<link rel="stylesheet" href="../../../../../stylesheets/atlas-cards.css">', card_page)
        self.assertIn("stylesheets/atlas-cards.css", site)
        topic = site[f"roadmap/{T}/index.html"].decode()
        self.assertIn('<p class="atlas-moved" id="main">This statement moved: <a href="c/index.html#main">Main</a>.'
                      '</p>', topic)
        self.assertIn('<script src="../../../../javascripts/atlas-card-moves.js"></script></head>', topic)
        self.assertIn("javascripts/atlas-card-moves.js", site)
        self.assertNotIn("atlas-card-moves.js", card_page)
        # The statement's old page of its own, a bare notice as trim_pages publishes render's own.
        notice = site[f"roadmap/{T}/main.html"].decode()
        self.assertTrue(notice.startswith("<!doctype html>"))
        self.assertIn('<p><a href="c/index.html#main">Continue to the mathematical page</a></p>', notice)


if __name__ == "__main__":
    unittest.main()
