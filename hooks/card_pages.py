"""Show each card on its folder page, and keep the addresses the card move ledger retired.

Cards (docs/cards.md) are derived in the wiki job itself: after lean-facts and before render,
`scripts/cards.py rollup` writes build/cards.json from the job's own checkout and extraction, and writes nothing
when the strict check finds an error. This hook reads that file only when it is an `atlas-cards/v1` rollup of the
commit being built (the checkout's HEAD), well formed, naming only pages the site publishes and agreeing with
itself where it restates itself (statuses and their rows, counts and their lists, clusters and `uses`), and only
when scripts/card-moves.jsonl leads every address it retired to a page the site publishes. Otherwise, or when
there is no card and no moved address to show, it changes nothing: the site is, byte for byte, the site without
cards, so no card data of another revision, and no part of a rollup, is ever shown.

With card data, the hook adds:

- on each card's folder page, before its first section, a block with the card's kind, importance and level, the
  status of its main statement, the progress of its other statements, the statements it presents from
  elsewhere, and each of its derived edges with the statements that witness it: the cards it uses and the cards
  that use it, the cards its main statement needs and the cards whose main statement needs it, each with its
  walk, and the cluster of mutually reachable cards it belongs to, with one cycle among them. It is HTML a
  reader without JavaScript reads as it is, with the witnesses in collapsed `<details>`;
- the redirects of the move ledger, all from one resolution of its history (history()), in which a folder row
  moves the folder alone and each page or folder inside it that moved has its own row, for every shape an old
  address had. A statement's old route was its box on its folder's page or a page of its own, and the ledger
  does not say which, so every moved statement keeps both: on its old folder page, if that still exists, an
  element with its old anchor holding a plain link to where it went, and a script that follows that link; and a
  notice page at `<old address>.html`. At the address of a folder that is gone, a notice page with a plain link to
  where the folder went and an element for each old anchor of its statements; at the old explorer page of a
  folder that is gone, a notice like the ones render writes for live folders; and
  `javascripts/atlas-card-moves.js`, a table of every old address and where it leads, which the pages an old
  explorer link `#node=<old address>` can reach load first, and which rewrites that selection before the explorer
  starts. An old anchor that an element of its old page has now, such as a section heading, stays that
  element's, and the build log says so;
- theme/stylesheets/atlas-cards.css, linked from every page when there is a block or an old anchor to style.
"""

from __future__ import annotations

import html
import json
import logging
import posixpath
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

log = logging.getLogger("mkdocs.hooks.card_pages")

# Relative to the folder of mkdocs.yml.
DATA = "build/cards.json"
LEDGER = "scripts/card-moves.jsonl"
# In the site source: render's search index, which gives every published page's route and title.
INDEX = "dependencies/index.json"
INDEX_SCHEMA = "autoform-dag-search/v1"
STYLE = "stylesheets/atlas-cards.css"
SCRIPT = "javascripts/atlas-card-moves.js"
SCHEMA = "atlas-cards/v1"
ROOT = "roadmap"
ARTICLE_ID = re.compile(r"af_[0-9a-f]{24}")
COMMIT = re.compile(r"[0-9a-f]{40}")
KINDS = {"concept": "Concept card", "result": "Result card"}
IMPORTANCE = ("landmark", "key", "supporting")
LEVELS = ("undergraduate", "graduate", "research")
# A statement's status as docs/cards.md gives it: the first marker that applies, then Autoform's state.
LABELS = {
    "stale": "stale",
    "held": "held",
    "not_ready": "not ready",
    "page_only": "page only",
    "mathlib": "in Mathlib",
    "fully_proved": "fully proved",
    "proved": "proved (not fully)",
    "defined": "defined",
    "conditional": "conditionally proved",
    "can_prove": "ready to prove",
    "stated": "stated, proof blocked",
    "can_state": "ready to state",
    "planned": "blocked, not ready to state",
}
# How a dependency is known, shown beside a witness that Lean did not compile between two ATLAS declarations.
ORIGINS = {
    "compiled": None,
    "planned": ("planned", "A prerequisite a planned page names"),
    "bridge": ("bridge", "From an ATLAS declaration to a Mathlib one"),
    "mathlib": ("Mathlib", "Between two Mathlib declarations"),
}
EDGE_KINDS = ("statement", "proof")
# Autoform's state keys a credited statement shows, after the markers; any other is shown as `planned`.
STATES = ("mathlib", "fully_proved", "proved", "defined", "conditional", "can_prove", "stated", "can_state", "planned")
CREDITS = ("atlas", "mathlib", "none")
# The rollup's accounting of the dependencies out of the cards' statements (docs/cards.md#derived-data).
ACCOUNTING = ("internal", "card_to_card", "to_unassigned", "to_subject_without_cards", "to_folder")

# On an old folder page: follow the link of the element the address's fragment names, when it is a moved one.
FOLLOW = ('(function(){var h=location.hash.slice(1),e;try{h=decodeURIComponent(h)}catch(x){}'
          'e=h&&document.getElementById(h);e=e&&e.classList.contains("atlas-moved")&&e.querySelector("a[href]");'
          'if(e)location.replace(e.href)})();')


class CardDataError(ValueError):
    """Card data the site cannot show as it is; the site then shows no card data at all."""


def need(condition: object, reason: str) -> None:
    if not condition:
        raise CardDataError(reason)


@dataclass(frozen=True)
class Node:
    """A page render publishes, as its search index gives it: a statement or a folder, the document it is in,
    from the site's root, its anchor there, and its title as the site shows it."""

    folder: bool
    path: str
    fragment: str
    title: str


@dataclass
class Site:
    """Everything the hook adds to one build: what goes into which page, by the page's published path, and the
    files it writes, by their path in the site source."""

    blocks: dict[str, str] = field(default_factory=dict)
    anchors: dict[str, list[tuple[str, str]]] = field(default_factory=dict)
    head: dict[str, str] = field(default_factory=dict)
    files: dict[str, str] = field(default_factory=dict)
    cards: int = 0
    addresses: int = 0
    # Old anchors an element of their old page has now: found while the pages are built.
    collisions: list[str] = field(default_factory=list)

    def empty(self) -> bool:
        return not (self.blocks or self.anchors or self.head or self.files)


def title_html(entry: dict) -> str:
    """A title as the site shows it: the index's text, code and formula parts when it has them, else its text,
    with Markdown code spans as code."""
    reading = entry.get("reading_title")
    if reading is not None:
        need(isinstance(reading, dict) and reading.get("format") == "inline-parts-v1"
             and isinstance(reading.get("parts"), list), "a title's parts are not inline-parts-v1")
        shown = []
        for part in reading["parts"]:
            need(isinstance(part, list) and len(part) == 2 and all(isinstance(value, str) for value in part),
                 "a title part is not a kind and a text")
            kind, value = part
            need(kind in ("text", "code", "math"), f"a title part has the kind {kind!r}")
            text = html.escape(value, quote=False)
            shown.append(text if kind == "text" else f"<code>{text}</code>" if kind == "code"
                         else f'<span class="arithmatex">{text}</span>')
        return "".join(shown)
    need(isinstance(entry.get("title"), str), "an index entry has no title")
    return code_spans(entry["title"])


def code_spans(text: str) -> str:
    """``text`` as HTML, a run of backticks and the next run of the same length around code, as Markdown reads
    a code span."""
    shown, at = [], 0
    for opening in re.finditer(r"`+", text):
        if opening.start() < at:
            continue
        closing = re.compile(rf"(?<!`){opening.group()}(?!`)").search(text, opening.end())
        if closing is None:
            continue
        code = text[opening.end():closing.start()]
        if code.strip() and code.startswith(" ") and code.endswith(" "):
            code = code[1:-1]
        shown += [html.escape(text[at:opening.start()], quote=False), f"<code>{html.escape(code, quote=False)}</code>"]
        at = closing.end()
    return "".join(shown) + html.escape(text[at:], quote=False)


def read_index(payload: object) -> dict[str, dict]:
    """Render's search index, by node id: each entry with the published document and anchor its route names."""
    need(isinstance(payload, dict) and payload.get("schema") == INDEX_SCHEMA and isinstance(payload.get("nodes"), list),
         f"render's search index is not {INDEX_SCHEMA}")
    entries = {}
    for entry in payload["nodes"]:
        need(isinstance(entry, dict) and isinstance(entry.get("id"), str) and entry.get("kind") in ("node", "scope")
             and isinstance(entry.get("route"), str), "an index entry has no id, kind or route")
        location, _, fragment = entry["route"].partition("#")
        path = posixpath.normpath(posixpath.join(posixpath.dirname(INDEX), unquote(location)))
        need(not urlsplit(location).scheme and not location.startswith("/") and path.endswith(".html")
             and not path.startswith("../"), f"the route of {entry['id']} leaves the site")
        entries[entry["id"]] = {**entry, "path": path, "fragment": unquote(fragment)}
    return entries


class Pages:
    """The pages render publishes, as the index names them, with their titles read when first asked for."""

    def __init__(self, entries: dict[str, dict]):
        self.entries = entries
        self.nodes: dict[str, Node] = {}

    def leaf(self, node_id: object) -> bool:
        return isinstance(node_id, str) and node_id in self.entries and self.entries[node_id]["kind"] == "node"

    def folder(self, node_id: object) -> bool:
        return isinstance(node_id, str) and node_id in self.entries and self.entries[node_id]["kind"] == "scope"

    def __getitem__(self, node_id: str) -> Node:
        if node_id not in self.nodes:
            entry = self.entries[node_id]
            self.nodes[node_id] = Node(entry["kind"] == "scope", entry["path"], entry["fragment"], title_html(entry))
        return self.nodes[node_id]


def href(page: str, node: Node) -> str:
    """A link from the published document ``page`` to ``node``."""
    target = "" if node.path == page else quote(posixpath.relpath(node.path, posixpath.dirname(page)), safe="/")
    if node.fragment:
        return f"{target}#{quote(node.fragment, safe='')}"
    return target or quote(posixpath.basename(page), safe="/")


def attribute(value: str) -> str:
    return html.escape(value, quote=True)


def plural(count: int, one: str, many: str | None = None) -> str:
    return f"{count} {one if count == 1 else many or one + 's'}"


def check_steps(steps: object, pages: Pages, what: str) -> list[dict]:
    """A list of typed dependencies between published statements: witnesses, or the steps of a walk."""
    need(isinstance(steps, list) and steps, f"{what} has no dependencies")
    for step in steps:
        need(isinstance(step, dict) and pages.leaf(step.get("source")) and pages.leaf(step.get("target"))
             and step.get("kind") in EDGE_KINDS and step.get("origin") in ORIGINS,
             f"{what} has a dependency that is not a typed edge between published statements")
    return steps


def bucket(row: dict) -> str:
    """A statement's status as docs/cards.md gives it, from its row of the rollup's `pages` table: the first marker
    that applies, then Autoform's state."""
    for marker, holds in (("stale", row["stale"]), ("held", row["held"]), ("not_ready", row["not_ready"]),
                          ("page_only", row["credit"] == "none")):
        if holds:
            return marker
    return row["state"] if row["state"] in STATES else "planned"


def components(cards, uses: set[tuple[str, str]]) -> list[list[str]]:
    """The strongly connected parts of ``uses`` with two cards or more, each sorted, in sorted order."""
    successors: dict[str, set[str]] = defaultdict(set)
    for source, target in uses:
        successors[source].add(target)
    reach = {}
    for card in cards:
        seen, frontier = set(), [card]
        while frontier:
            for target in successors[frontier.pop()]:
                if target not in seen:
                    seen.add(target)
                    frontier.append(target)
        reach[card] = seen
    parts = {tuple(sorted({card} | {other for other in reach[card] if card in reach[other]})) for card in cards}
    return sorted(list(part) for part in parts if len(part) > 1)


def check_data(data: object, pages: Pages) -> dict[str, dict]:
    """The cards of a rollup, by id, once every part the site shows is well formed, names a card it holds or a page
    render publishes, and agrees with the parts that restate it: each status with the statement's row in the `pages`
    table, each count with what it counts, and the clusters with the strongly connected parts of `uses`. A
    CardDataError otherwise."""
    need(isinstance(data, dict) and data.get("schema") == SCHEMA, f"the card data is not {SCHEMA}")
    for key in ("cards", "uses", "needs", "clusters"):
        need(isinstance(data.get(key), list), f"the card data has no `{key}` list")
    table = data.get("pages")
    need(isinstance(table, dict), "the card data has no `pages` table")

    def row(node_id: str) -> dict:
        found = table.get(node_id)
        need(isinstance(found, dict) and found.get("credit") in CREDITS
             and all(isinstance(found.get(key), bool) for key in ("held", "not_ready", "stale"))
             and (found.get("state") is None or isinstance(found.get("state"), str)),
             f"{node_id} has no well-formed row in the `pages` table")
        return found

    cards: dict[str, dict] = {}
    home: dict[str, str] = {}
    for card in data["cards"]:
        need(isinstance(card, dict) and isinstance(card.get("id"), str) and ARTICLE_ID.fullmatch(card["id"]),
             "a card has no id")
        where = card["id"]
        need(where not in cards, f"{where} is listed twice")
        need(pages.folder(card.get("folder")), f"{where}: its folder is no folder page the site publishes")
        need(card.get("kind") in KINDS and card.get("importance") in IMPORTANCE and card.get("level") in LEVELS,
             f"{where}: its kind, importance or level is unknown")
        main = card.get("main")
        need(isinstance(main, dict) and main.get("headline") in LABELS, f"{where}: its main statement has no status")
        members = card.get("pages")
        need(isinstance(members, list) and members and all(pages.leaf(member) for member in members)
             and len(set(members)) == len(members), f"{where}: its statements are not published statement pages")
        need(all(member.rsplit("/", 1)[0] == card["folder"] for member in members),
             f"{where}: a statement is not a page of its folder")
        need(main.get("page") in members, f"{where}: its main statement is not one of its statements")
        supports = card.get("supports", [])
        need(isinstance(supports, list) and all(pages.leaf(other) for other in supports),
             f"{where}: it presents a page that is no published statement")
        supporting = card.get("supporting")
        need(isinstance(supporting, dict) and all(isinstance(supporting.get(key), int) and supporting[key] >= 0
                                                  for key in ("total", *LABELS))
             and sum(supporting[key] for key in LABELS) == supporting["total"] == len(members) - 1,
             f"{where}: the progress of its supporting statements does not add up")
        # The statuses restate the `pages` table: the main statement's headline and markers, and the progress of
        # the other statements.
        own = row(main["page"])
        need(all(main.get(key) == own[key] for key in ("credit", "held", "not_ready", "stale", "state"))
             and main["headline"] == bucket(own), f"{where}: its main statement's status is not its row's")
        counted = Counter(bucket(row(member)) for member in members if member != main["page"])
        need(all(supporting[key] == counted.get(key, 0) for key in LABELS),
             f"{where}: the progress of its supporting statements is not their rows'")
        for other in supports:
            row(other)
        cards[where] = card
        for member in members:
            need(member not in home, f"{member} is a statement of two cards")
            need(row(member).get("card") == where, f"{member}: its row names another card")
            home[member] = where
    joined: dict[str, set] = {"uses": set(), "needs": set()}
    for edge in data["uses"]:
        need(isinstance(edge, dict) and edge.get("from") in cards and edge.get("to") in cards
             and edge["from"] != edge["to"] and (edge["from"], edge["to"]) not in joined["uses"],
             "a `uses` edge does not join two cards, or is listed twice")
        joined["uses"].add((edge["from"], edge["to"]))
        witnesses = check_steps(edge.get("witnesses"), pages, f"the `uses` edge {edge['from']} -> {edge['to']}")
        need(all(home.get(step["source"]) == edge["from"] and home.get(step["target"]) == edge["to"]
                 for step in witnesses), f"a witness of {edge['from']} -> {edge['to']} joins other cards")
        need(all(edge.get(kind) == sum(step["kind"] == kind for step in witnesses) for kind in EDGE_KINDS)
             and edge.get("origins") == dict(Counter(step["origin"] for step in witnesses))
             and len({(step["source"], step["target"], step["kind"]) for step in witnesses}) == len(witnesses),
             f"the counts of {edge['from']} -> {edge['to']} are not its witnesses'")
        for step in witnesses:
            row(step["source"]), row(step["target"])
    mains = {card["main"]["page"] for card in cards.values()}
    for edge in data["needs"]:
        need(isinstance(edge, dict) and edge.get("from") in cards and edge.get("to") in cards
             and edge["from"] != edge["to"] and (edge["from"], edge["to"]) not in joined["needs"]
             and edge.get("phase") in EDGE_KINDS, "a `needs` edge does not join two cards, or is listed twice")
        joined["needs"].add((edge["from"], edge["to"]))
        key = "statement_walk" if edge["phase"] == "statement" else "walk"
        steps = check_steps(edge.get(key), pages, f"the `needs` edge {edge['from']} -> {edge['to']}")
        need(steps[0]["source"] == cards[edge["from"]]["main"]["page"]
             and steps[-1]["target"] == cards[edge["to"]]["main"]["page"]
             and all(one["target"] == two["source"] for one, two in zip(steps, steps[1:]))
             and not any(step["target"] in mains for step in steps[:-1]),
             f"the walk of {edge['from']} -> {edge['to']} is not a walk between their main statements through "
             "statements that head no card")
        for step in steps:
            row(step["source"]), row(step["target"])
        # A statement walk has statement steps only; a proof walk exists only when there is none, so it has a
        # proof step.
        kinds = {step["kind"] for step in steps}
        need(kinds == {"statement"} if edge["phase"] == "statement" else "proof" in kinds,
             f"the walk of {edge['from']} -> {edge['to']} does not have the steps its phase says")
    clustered: set[str] = set()
    for cluster in data["clusters"]:
        need(isinstance(cluster, dict) and isinstance(cluster.get("cards"), list) and len(cluster["cards"]) > 1
             and all(card in cards and card not in clustered for card in cluster["cards"]),
             "a cluster does not hold two cards or more, or shares one with another cluster")
        clustered.update(cluster["cards"])
        cycle = cluster.get("example_cycle")
        need(isinstance(cycle, list) and len(cycle) > 2 and cycle[0] == cycle[-1]
             and all(card in cluster["cards"] for card in cycle)
             and all(pair in joined["uses"] for pair in zip(cycle, cycle[1:])),
             "an example cycle is not a closed walk of `uses` edges inside its cluster")
        inner = sorted([source, target] for source, target in joined["uses"]
                       if source in cluster["cards"] and target in cluster["cards"])
        need(sorted(map(list, cluster.get("edges") or [])) == inner,
             "a cluster's edges are not the `uses` edges between its cards")
    need(sorted(sorted(cluster["cards"]) for cluster in data["clusters"]) == components(cards, joined["uses"]),
         "the clusters are not the strongly connected parts of `uses`")
    # A statement's row names its card only if the card holds it.
    need(all(entry.get("card") is None or home.get(node_id) == entry.get("card")
             for node_id, entry in table.items() if isinstance(entry, dict)),
         "a row of the `pages` table names a card that does not hold its statement")
    # The counts restate the lists, and the accounting of the cards' dependencies adds up to its witnesses.
    unassigned = data.get("unassigned", [])
    need(isinstance(unassigned, list) and all(isinstance(entry, dict) and isinstance(entry.get("pages"), list)
                                              for entry in unassigned), "the card data's `unassigned` is malformed")
    counts = data.get("counts")
    expected = {"cards": len(cards), "pages": len(home), "uses": len(data["uses"]), "needs": len(data["needs"]),
                "clusters": len(data["clusters"]), "unassigned": sum(len(entry["pages"]) for entry in unassigned)}
    need(isinstance(counts, dict) and all(counts.get(key) == value for key, value in expected.items()),
         "the card data's counts are not those of its lists")
    accounting = data.get("edges")
    need(isinstance(accounting, dict) and all(isinstance(accounting.get(key, 0), int) for key in (*ACCOUNTING, "total"))
         and accounting.get("total", 0) == sum(accounting.get(key, 0) for key in ACCOUNTING)
         and accounting.get("card_to_card", 0) == sum(len(edge["witnesses"]) for edge in data["uses"]),
         "the card data's accounting of dependencies does not add up to its witnesses")
    return cards


@dataclass
class Ledger:
    """scripts/card-moves.jsonl: its rows in order, each ("page", old, new), ("folder", old, new) or ("card", card,
    folder, replaced_by), and each retired card's last address and replacement."""

    rows: list[tuple[str, ...]] = field(default_factory=list)
    retired: dict[str, tuple[str, str]] = field(default_factory=dict)


def valid_address(value: object) -> bool:
    return (isinstance(value, str) and bool(value) and not value.startswith("/") and not value.endswith(".md")
            and all(part and part not in (".", "..") for part in value.split("/")))


def read_ledger(text: str) -> Ledger:
    """The ledger's rows, in order. A page or folder address moves once and a card is retired once; a folder may be
    the last address of several retired cards, each replaced in place by the next (docs/cards.md#move-ledger)."""
    ledger = Ledger()
    moved: set[tuple[str, str]] = set()
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            raise CardDataError(f"{LEDGER}:{number}: not JSON") from error
        need(isinstance(row, dict), f"{LEDGER}:{number}: not an object")
        kind = next((kind for kind in ("page", "folder") if set(row) == {kind, "to", "article_id"}), None)
        if kind is not None:
            need(valid_address(row[kind]) and valid_address(row["to"]) and (kind, row[kind]) not in moved,
                 f"{LEDGER}:{number}: a malformed or repeated {kind} row")
            moved.add((kind, row[kind]))
            ledger.rows.append((kind, row[kind], row["to"]))
        else:
            need(set(row) == {"card", "folder", "replaced_by"} and valid_address(row["folder"])
                 and isinstance(row["card"], str) and isinstance(row["replaced_by"], str)
                 and row["card"] not in ledger.retired,
                 f"{LEDGER}:{number}: not a page, folder or retirement row, or a repeated one")
            ledger.retired[row["card"]] = (row["folder"], row["replaced_by"])
            ledger.rows.append(("card", row["card"], row["folder"], row["replaced_by"]))
    return ledger


def parent(address: str) -> str:
    return address.rsplit("/", 1)[0] if "/" in address else ROOT


def ancestors(address: str):
    """The folders above ``address``, nearest first, the roadmap's own last."""
    while address != ROOT:
        address = parent(address)
        yield address


def history(ledger: Ledger, pages: Pages, cards: dict[str, dict]) -> dict[tuple[str, str], str]:
    """Every address the ledger's history gave a statement page or a folder and the site no longer publishes, by
    kind (`page` or `folder`) and address, with the published statement or folder it leads to now.

    The rows are replayed backwards from the pages the site publishes, so that every address is followed through
    every row after it, in order. Each page or folder row puts its old address in the place of its new one. A
    folder row moves the folder alone: each page and folder inside it that moved has its own row
    (docs/cards.md#move-ledger), so no address is inferred from what a folder holds, and a page added to a folder
    after it moved gets no old address. A retired card's folder that is gone leads to the folder of the live card
    its replacements end at, as scripts/cards.py follows them; a folder that held a moved address and is gone with
    no row of its own leads where its nearest enclosing folder leads at that point. An address the rows lead to no
    published page or folder is an error."""
    where = {("page" if entry["kind"] == "node" else "folder", node_id): node_id
             for node_id, entry in pages.entries.items()}
    found: dict[tuple[str, str], str] = {}

    def replacement(card: str) -> str:
        seen = {card}
        while card in ledger.retired:
            card = ledger.retired[card][1]
            need(card not in seen, f"{LEDGER}: the replacements of a retired card go round")
            seen.add(card)
        need(card in cards, f"{LEDGER}: a retired card's replacements end at {card}, which is no card of the rollup")
        return cards[card]["folder"]

    def enclosed(address: str) -> None:
        """The folders that held ``address`` at this point: one that is gone leads where the nearest one that is
        not leads."""
        missing = []
        for above in ancestors(address):
            if ("folder", above) in where:
                for folder in missing:
                    where[("folder", folder)] = found[("folder", folder)] = where[("folder", above)]
                return
            missing.append(above)
        raise CardDataError(f"{LEDGER}: {address} is in no published folder")

    for row in reversed(ledger.rows):
        if row[0] == "page":
            _, old, new = row
            need(("page", new) in where, f"{LEDGER}: the page {old} leads to {new}, which is no published statement")
            where[("page", old)] = found[("page", old)] = where.pop(("page", new))
            enclosed(old)
        elif row[0] == "folder":
            # A folder row moves the folder alone: each page and folder inside it that moved has its own row, and a
            # page added to the folder later has none, so it gets no old address.
            _, old, new = row
            need(("folder", new) in where, f"{LEDGER}: the folder {old} leads to {new}, which is no published folder")
            where[("folder", old)] = found[("folder", old)] = where.pop(("folder", new))
            enclosed(old)
        else:
            _, card, folder, _ = row
            if ("folder", folder) not in where:
                where[("folder", folder)] = found[("folder", folder)] = replacement(card)
            enclosed(folder)
    return {key: endpoint for key, endpoint in found.items()
            if not (pages.leaf(key[1]) if key[0] == "page" else pages.folder(key[1]))}


def walk_phrase(steps: list[dict]) -> str:
    """How a walk between two main statements goes, read from its steps."""
    return "through a proof" if any(step["kind"] == "proof" for step in steps) else "through statements"


def walk_html(page: str, pages: Pages, step: dict) -> str:
    """One typed dependency: which statement uses which, in its statement or in its proof, and how it is known
    when Lean did not compile it between two ATLAS declarations."""
    source, target = pages[step["source"]], pages[step["target"]]
    origin = ORIGINS[step["origin"]]
    known = "" if origin is None else (f' <span class="atlas-card-origin" title="{attribute(origin[1])}">'
                                       f"{origin[0]}</span>")
    return (f'<a href="{attribute(href(page, source))}">{source.title}</a> uses '
            f'<a href="{attribute(href(page, target))}">{target.title}</a> in its {step["kind"]}{known}')


class Cards:
    """The block each card's folder page shows."""

    def __init__(self, data: dict, cards: dict[str, dict], pages: Pages):
        self.cards, self.pages = cards, pages
        self.edges: dict[tuple[str, str], list[tuple[str, dict]]] = defaultdict(list)
        for key, other, relation in (("uses", "to", "uses"), ("uses", "from", "used by"), ("needs", "to", "needs"),
                                     ("needs", "from", "needed by")):
            for edge in data[key]:
                self.edges[(edge["from" if other == "to" else "to"], relation)].append((edge[other], edge))
        self.uses = {(edge["from"], edge["to"]): edge for edge in data["uses"]}
        self.cluster = {card: cluster for cluster in data["clusters"] for card in cluster["cards"]}

    def page(self, card: str) -> str:
        return self.pages[self.cards[card]["folder"]].path

    def card_link(self, page: str, card: str) -> str:
        folder = self.pages[self.cards[card]["folder"]]
        return f'<a href="{attribute(href(page, folder))}">{folder.title}</a>'

    def link(self, page: str, node_id: str) -> str:
        node = self.pages[node_id]
        return f'<a href="{attribute(href(page, node))}">{node.title}</a>'

    def steps(self, page: str, steps: list[dict], tag: str = "ul") -> str:
        items = "".join(f"<li>{walk_html(page, self.pages, step)}</li>" for step in steps)
        return f"<{tag}>{items}</{tag}>"

    def relation(self, page: str, card: str, relation: str) -> str:
        """The cards ``card`` has ``relation`` to, each a collapsed list of the dependencies that witness it."""
        found = sorted(self.edges[(card, relation)], key=lambda pair: pair[0])
        if not found:
            return ""
        items = []
        for other, edge in found:
            if relation in ("uses", "used by"):
                about = ", ".join(plural(edge[kind], f"{kind} use") for kind in EDGE_KINDS if edge[kind])
                witnesses = self.steps(page, edge["witnesses"])
            else:
                walk = edge["statement_walk" if edge["phase"] == "statement" else "walk"]
                about, witnesses = walk_phrase(walk), self.steps(page, walk, "ol")
            items.append(f"<details><summary>{self.card_link(page, other)} · {about}</summary>{witnesses}</details>")
        return f"<dt>{relation.capitalize()}</dt><dd>{''.join(items)}</dd>"

    def block(self, card_id: str) -> str:
        card = self.cards[card_id]
        page = self.page(card_id)
        main = card["main"]
        headline = main["headline"]
        parts = [
            f'<p class="atlas-card-facts"><strong>{KINDS[card["kind"]]}</strong> · importance: {card["importance"]} '
            f'· level: {card["level"]}</p>',
            f'<p>Main statement: {self.link(page, main["page"])}: <span class="atlas-card-state '
            f'atlas-card-{headline}">{LABELS[headline]}</span></p>',
        ]
        supporting = card["supporting"]
        if supporting["total"]:
            buckets = ", ".join(f"{supporting[key]} {LABELS[key]}" for key in LABELS if supporting[key])
            parts.append(f"<p>{plural(supporting['total'], 'supporting statement')}: {buckets}</p>")
        else:
            parts.append("<p>No supporting statement.</p>")
        if card.get("supports"):
            presented = ", ".join(self.link(page, other) for other in card["supports"])
            parts.append(f"<p>Also presents: {presented}</p>")
        edges = "".join(self.relation(page, card_id, relation)
                        for relation in ("uses", "used by", "needs", "needed by"))
        cluster = self.cluster.get(card_id)
        if cluster is not None:
            cycle = cluster["example_cycle"]
            members = ", ".join(self.card_link(page, member) for member in cluster["cards"])
            walk = " → ".join(self.card_link(page, member) for member in cycle)
            steps = "".join(f"<li>{self.card_link(page, one)} uses {self.card_link(page, two)}:"
                            f"{self.steps(page, self.uses[(one, two)]['witnesses'])}</li>"
                            for one, two in zip(cycle, cycle[1:]))
            # A cluster is a strongly connected part of `uses`: each of its cards reaches every other one, though
            # no single cycle need pass through them all; its example cycle is one cycle among them.
            edges += (f"<dt>In a mutually reachable group of {len(cluster['cards'])} cards</dt><dd><p>Each of these "
                      f"cards uses every other one, directly or through cards of the group: {members}. One cycle "
                      f"among them: {walk}.</p><details><summary>The dependencies of this cycle</summary><ul>{steps}"
                      "</ul></details></dd>")
        parts.append(f'<dl class="atlas-card-edges">{edges}</dl>' if edges else
                     "<p>No other card uses this one, and this one uses no other card.</p>")
        return f'<div class="atlas-card">{"".join(parts)}</div>'


def moved_element(slug: str, page: str, target: Node) -> str:
    return (f'<p class="atlas-moved" id="{attribute(slug)}">This statement moved: '
            f'<a href="{attribute(href(page, target))}">{target.title}</a>.</p>')


def notice(page: str, target: str, elements: list[str]) -> str:
    """A notice page at a retired address, in the form of render's own notices for old explorer pages, which
    trim_pages publishes as a bare document: a plain link to ``target``, and an element for each old anchor. Its
    script follows the link of the element the address's fragment names, or else the plain link with the
    fragment when ``target`` has none; without elements, a refresh does the same for a reader without
    JavaScript."""
    script = ('(function(){var h=location.hash.slice(1),e,to;try{h=decodeURIComponent(h)}catch(x){}'
              'e=h&&document.getElementById(h);e=e&&e.classList.contains("atlas-moved")&&e.querySelector("a[href]");'
              f'to=new URL(e?e.getAttribute("href"):{json.dumps(target)},location.href);'
              'if(!e&&!to.hash)to.hash=location.hash;location.replace(to.href)})();')
    lines = ["---", "title: This page moved", "search:", "  exclude: true", "hide:", "  - navigation", "  - toc", "---",
             "", "# This page moved", "", '<div class="bp-moved">',
             f'<div class="bp-dag-viewer" data-page-href="{attribute(target)}" hidden></div>',
             f'<p><a href="{attribute(target)}">Continue to the mathematical page</a></p>', *elements,
             f"<script>{script}</script>"]
    if not elements:
        lines.append(f'<noscript><meta http-equiv="refresh" content="0; url={attribute(target)}"></noscript>')
    return "\n".join([*lines, "</div>"]) + "\n"


def source_path(path: str) -> str:
    """The site source file a published document comes from."""
    return path[:-len("index.html")] + "README.md" if path.endswith("/index.html") else path[:-len(".html")] + ".md"


def moves_script(moves: dict[str, str]) -> str:
    """The explorer's rewrite: ``moves`` maps every old address the ledger's history gave a statement or a folder to
    the one it leads to now, as history() resolves it."""
    table = json.dumps(moves, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return (
        "/* Written by hooks/card_pages.py from scripts/card-moves.jsonl. An explorer link #node=<old address> is\n"
        "   rewritten to where the address leads before the explorer starts. */\n"
        '(function () {\n  "use strict";\n'
        f"  var moves = {table}, own = Object.prototype.hasOwnProperty;\n"
        '  var hash = new URLSearchParams(location.hash.slice(1)), node = hash.get("node");\n'
        "  if (node === null) return;\n"
        "  var kind = /^(?:scope|boundary):/.exec(node), lead = kind ? kind[0] : \"\", at = node.slice(lead.length);\n"
        "  if (!own.call(moves, at)) return;\n"
        '  hash.set("node", lead + moves[at]);\n'
        '  history.replaceState(history.state, "", "#" + hash.toString());\n'
        "})();\n"
    )


def redirects(site: Site, ledger: Ledger, pages: Pages, cards: dict[str, dict], docs: Path) -> None:
    """The redirects of the move ledger, added to ``site``, all from one resolution of its history."""
    found = history(ledger, pages, cards)
    # A statement's old route was its box on its folder's page or a page of its own, by whether it had a
    # declaration kind then; the ledger does not say which, and a statement credited or uncredited since has another
    # route now. So every old address of a statement keeps both: its old anchor and a notice at `<address>.html`.
    leaves_in: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for (kind, address), endpoint in sorted(found.items()):
        if kind != "page":
            continue
        folder, slug = parent(address), address.rsplit("/", 1)[-1]
        leaves_in[folder].append((slug, endpoint))
        page = f"{ROOT}/{address}.html"
        site.files[source_path(page)] = notice(page, href(page, pages[endpoint]), [])
        if pages.folder(folder):
            folder_page = pages[folder].path
            site.anchors.setdefault(folder_page, []).append((slug, moved_element(slug, folder_page, pages[endpoint])))
    # A folder that is gone: a notice with an element for each old anchor of its statements, and its old explorer
    # page, as render writes those of the live folders.
    for (kind, folder), endpoint in sorted(found.items()):
        if kind != "folder":
            continue
        page = f"{ROOT}/{folder}/index.html"
        elements = [moved_element(slug, page, pages[target]) for slug, target in sorted(leaves_in[folder])]
        site.files[source_path(page)] = notice(page, href(page, pages[endpoint]), elements)
        scope = f"dependencies/scopes/{folder}.md"
        if not (docs / scope).exists():
            explorer = f"dependencies/scopes/{folder}.html"
            site.files[scope] = notice(explorer, href(explorer, pages[endpoint]), [])
    if found:
        # An explorer link names a node; a statement and a folder beside it with its name share one, and the
        # statement's way is kept.
        table = {address: endpoint for (kind, address), endpoint in sorted(found.items()) if kind == "folder"}
        table.update({address: endpoint for (kind, address), endpoint in sorted(found.items()) if kind == "page"})
        site.files[SCRIPT] = moves_script(table)
        # The pages an old explorer link reaches: the published folders above each old address (render's notices for
        # old explorer pages lead there) and where each folder that is gone leads.
        landing = {endpoint for (kind, _), endpoint in found.items() if kind == "folder"}
        for _, address in found:
            landing.update(folder for folder in ancestors(address) if pages.folder(folder))
        for folder in sorted(landing):
            page = pages[folder].path
            source = posixpath.relpath(SCRIPT, posixpath.dirname(page))
            site.head[page] = f'<script src="{attribute(quote(source, safe="/"))}"></script>'
    for path in [*site.files, STYLE]:
        need(not (docs / path).exists(), f"the site source already has {path}")
    site.addresses = len(found)


def build(data: object, index: object, ledger_text: str, docs: Path) -> Site:
    """What the hook adds for a rollup ``data``, given render's search index and the move ledger; a CardDataError
    when any part of it cannot be shown as it is."""
    pages = Pages(read_index(index))
    cards = check_data(data, pages)
    site = Site(cards=len(cards))
    shown = Cards(data, cards, pages)
    for card_id in sorted(cards):
        site.blocks[shown.page(card_id)] = shown.block(card_id)
    redirects(site, read_ledger(ledger_text), pages, cards, docs)
    return site


def head_commit(root: Path) -> str | None:
    try:
        commit = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], check=True, capture_output=True,
                                text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None
    return commit if COMMIT.fullmatch(commit) else None


class Reading(HTMLParser):
    """Where a page's reading (render's `div.bp-reading-source`) has its first section heading, and where it
    ends."""

    def __init__(self, text: str):
        super().__init__(convert_charrefs=False)
        self.starts = [0, *(match.end() for match in re.finditer("\n", text))]
        self.depth = 0
        self.first_h2: int | None = None
        self.end: int | None = None
        self.feed(text)
        self.close()

    def at(self) -> int:
        line, column = self.getpos()
        return self.starts[line - 1] + column

    def handle_starttag(self, tag, attrs):
        if self.end is not None:
            return
        if self.depth:
            if tag == "div":
                self.depth += 1
            elif tag == "h2" and self.first_h2 is None:
                self.first_h2 = self.at()
        elif tag == "div" and "bp-reading-source" in (dict(attrs).get("class") or "").split():
            self.depth = 1

    def handle_endtag(self, tag):
        if self.depth and tag == "div":
            self.depth -= 1
            if not self.depth:
                self.end = self.at()


def reading(text: str) -> Reading | None:
    """The reading of a page, or None when it cannot be read: the hook then appends what it adds."""
    try:
        return Reading(text)
    except Exception:  # noqa: BLE001 - a page the parser cannot read still gets its card data, at its end
        return None


def insert(text: str, at: int | None, added: str) -> str:
    return text + added if at is None else text[:at] + added + text[at:]


_site: Site | None = None


def on_config(config):
    global _site
    _site = None
    root = Path(config.config_file_path).resolve().parent
    data_file = root / DATA
    if not data_file.is_file():
        log.info("No card data: the site shows no card")
        return config
    try:
        data = json.loads(data_file.read_text(encoding="utf-8"))
        commit = head_commit(root)
        need(commit is not None and isinstance(data, dict) and data.get("commit") == commit,
             f"{DATA} is not the rollup of the commit being built")
        docs = Path(config.docs_dir)
        ledger = root / LEDGER
        site = build(data, json.loads((docs / INDEX).read_text(encoding="utf-8")),
                     ledger.read_text(encoding="utf-8") if ledger.is_file() else "", docs)
    except Exception as error:  # noqa: BLE001 - card data never fails the build: the site then shows none
        log.info("Card data not shown, so the site shows no card: %s", error)
        return config
    if site.empty():
        log.info("Card data with no card and no moved address: the site is as without card data")
        return config
    _site = site
    # The block and the old anchors need the stylesheet; every page links it, as the explorer moves between pages
    # without reloading their heads.
    if site.blocks or site.anchors:
        config.extra_css.append(STYLE)
    log.info("Cards shown: %d cards, %d retired addresses kept", site.cards, site.addresses)
    return config


def on_files(files, *, config):
    if _site is None:
        return files
    from mkdocs.structure.files import File

    for path, content in sorted(_site.files.items()):
        files.append(File.generated(config, path, content=content))
    return files


def on_page_content(html_text, *, page, config, files):
    if _site is None:
        return html_text
    path = page.file.dest_uri
    if path in _site.blocks:
        # Before the page's first section, after its opening: in its reading, which the explorer shows.
        found = reading(html_text)
        at = None if found is None else found.first_h2 if found.first_h2 is not None else found.end
        html_text = insert(html_text, at, _site.blocks[path])
    if path in _site.anchors:
        ids = set(re.findall(r'\sid="([^"]*)"', html_text))
        elements = []
        for slug, element in sorted(_site.anchors[path]):
            if slug in ids:
                # The old address is ambiguous: an element of the page has the id now, such as a section heading.
                # The page's own element keeps it, and the build log says so.
                log.info("Card moves: %s#%s now names an element of that page, which keeps it; the statement that "
                         "left keeps its other old routes", path, slug)
                _site.collisions.append(f"{path}#{slug}")
                continue
            elements.append(element)
        if elements:
            found = reading(html_text)
            html_text = insert(html_text, None if found is None else found.end,
                               f'<div class="atlas-moved-list">{"".join(elements)}<script>{FOLLOW}</script></div>')
    return html_text


def on_post_page(output, *, page, config):
    if _site is None or page.file.dest_uri not in _site.head:
        return output
    return output.replace("</head>", f"{_site.head[page.file.dest_uri]}</head>", 1)
