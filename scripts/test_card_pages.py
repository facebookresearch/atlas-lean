"""The site's cards (docs/cards.md#reading): hooks/card_pages.py shows card data only from a rollup of the commit being
built, shows each card's derived edges with their witnesses, and keeps every address the move ledger retired."""

from __future__ import annotations

import importlib.util
import json
import logging
import posixpath
import shutil
import subprocess
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path

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
    being built, the site is byte for byte the site without the card hook."""

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

    @classmethod
    def build(cls, configuration: str, data: dict | str | None, rows: str = LEDGER) -> dict[str, bytes]:
        from mkdocs.commands.build import build
        from mkdocs.config import load_config

        (cls.root / "scripts" / "card-moves.jsonl").write_text(rows, encoding="utf-8")
        cards = cls.root / "build" / "cards.json"
        cards.unlink(missing_ok=True)
        if data is not None:
            cards.parent.mkdir(exist_ok=True)
            cards.write_text(data if isinstance(data, str) else json.dumps(data), encoding="utf-8")
        site = cls.root / "site"
        shutil.rmtree(site, ignore_errors=True)
        build(load_config(str(cls.root / configuration), site_dir=str(site)))
        return {path.relative_to(site).as_posix(): path.read_bytes() for path in sorted(site.rglob("*"))
                if path.is_file()}

    def data(self, commit: str | None = None) -> dict:
        return rollup([card(1, f"{T}/c", ["main"])], commit=commit or self.commit)

    def test_without_card_data_of_this_commit_the_site_is_unchanged(self) -> None:
        bad = self.data()
        bad["cards"][0]["pages"] = [f"{T}/c/main", f"{T}/c/unpublished"]
        for name, data in (("no card data", None), ("another commit's", self.data(COMMIT)), ("not JSON", "{"),
                           ("a bad card", bad), ("another schema", {**self.data(), "schema": "atlas-cards/v0"})):
            with self.subTest(name):
                self.assertEqual(self.build("mkdocs.yml", data), self.baseline)

    def test_a_rollup_with_nothing_to_show_changes_nothing(self) -> None:
        # Before any card merges, the rollup of the commit passes with no card, and the ledger is empty.
        with self.assertLogs("mkdocs.hooks.card_pages", "INFO") as logged:
            self.assertEqual(self.build("mkdocs.yml", rollup([], commit=self.commit), ""), self.baseline)
        self.assertIn("Card data with no card and no moved address", "\n".join(logged.output))

    def test_moved_addresses_are_kept_with_no_card(self) -> None:
        site = self.build("mkdocs.yml", rollup([], commit=self.commit))
        topic = site[f"roadmap/{T}/index.html"].decode()
        self.assertIn('<p class="atlas-moved" id="main">', topic)
        self.assertIn('href="../../../../stylesheets/atlas-cards.css"', topic)
        self.assertNotIn("atlas-card\"", site[f"roadmap/{T}/c/index.html"].decode())

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
