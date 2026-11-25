#!/usr/bin/env python3
"""Cards: the wiki's reading level, above its statement pages.

    python scripts/cards.py check [--dependencies FILE [--registry FILE]]
           [--base-ledger FILE --base-links DIR --renames FILE]     validate the cards and the move ledger
    python scripts/cards.py rollup OUTPUT.json --dependencies FILE [--registry FILE]
           [--base-ledger FILE --base-links DIR --renames FILE]     check, then write the derived card data
    python scripts/cards.py moves OUTPUT.json                        check the move ledger alone, then write its receipt

A card is one idea a reader navigates by: a concept card (a definition that a textbook would give its own
paragraph) or a result card (a theorem worth naming or citing). It is a folder below blueprint/roadmap/ whose
folder page's annotation carries a card record, `extensions["org.atlas-wiki"]["card"]`; its statement pages are
the pages of that folder, and one of them is its main statement. The folder page credits no declaration, so
Autoform's counts, readiness and work list are unchanged: the statement pages stay the formal layer.
docs/cards.md gives the format, the identity rules and the meaning of the derived data.

The derived data is a build output, never committed. `uses` joins two cards when a statement of one depends on a
statement of the other and keeps every such dependency as a typed witness; it may contain cycles, which are
reported as clusters. `needs` joins two cards when the first one's main statement reaches the other's through
statements that are no card's main statement, with a walk that shows it, and is acyclic because Autoform's graph
is. Readiness stays Autoform's, on the statement pages.

Run both commands on the build's checkout after `sync_wiki.py lean-facts`, as the `check the cards` job does: the
dependencies are the ones lean-facts writes into the pages, and the declaration kinds the check compares with a
card's kind are the ones it writes into the annotations. The committed annotations (read with `git show HEAD:`)
say which pages the authors credited, so that a link lean-facts dropped shows as stale rather than as a planned
page. With --dependencies (the strict check, which rollup always runs), every dependency of an ATLAS-credited page
must be a typed edge the given extraction recorded and every edge it recorded between pages a dependency, and the
move ledger must exist; an edge this extraction cannot vouch for (from an ATLAS-credited page to a Mathlib-credited
one, or any edge a Mathlib-credited page lists) is an error unless --registry gives the build's Mathlib registry,
whose bridges and Mathlib edges those edges must then equal, while the registry must have been made from the
committed rows' credited names and find exactly the declarations the build's pages credit to Mathlib, one page each
with the registry's kind and the declaration its committed row credits, and a Mathlib main heads a result card
exactly when its type is a proposition; so every derived edge is `compiled`, `bridge` or `mathlib` (checked) or, from a page-only
page, `planned`. With --base-ledger, the ledger the base commit published
must stay the first rows of the ledger; with --base-links (the base commit's blueprint/links/) and --renames (`git
diff --name-status -M BASE HEAD -- blueprint/roadmap`), every change since the base commit is checked against the
rows added since. Run
with a Python that has Autoform and the site's Markdown extensions installed (see blueprint-pages.yml).

The wiki job runs rollup the same way before render, for the card data the site shows (hooks/card_pages.py):
rollup removes its output first and writes it, whole, only once the check passed, so an error leaves no card data.

moves checks scripts/card-moves.jsonl on its own, with check_moves and no base: against the annotations and the
roadmap as checked out, with no card or dependency check, so the site's redirects do not wait for the cards. Without
a base it certifies the present snapshot only; that the ledger only grows, and the moves since the base commit, stay
the strict check's. A missing ledger is an error, an empty one has no row. It reads each input file once, removes
its output first, and on success writes, whole, the receipt hooks/card_pages.py keeps the moved addresses with: the
commit, the sha256 of the ledger's bytes and a digest of the links folder's (links_digest), which bind the receipt to
the very inputs checked; the cards, by id, with their folders (`cards_complete` says whether that lists them all: a
card is listed only with an article id no other article has and a folder the site can serve); and the replacements,
the live article each retirement, of a card or of a statement, ends at, by id, with its kind and node, each at an
address the site can serve. It refuses outside a Git checkout.

A planned statement page may record its counterparts under `extensions["org.atlas-wiki"]["counterpart"]`
(docs/cards.md#counterparts): check verifies their form and their place, a live statement page Autoform reads whose
own row links no Lean declaration; they are data only, and nothing else here reads them.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from collections import Counter, defaultdict
from urllib.parse import unquote, urlsplit
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath

if __package__:
    from . import extract_v2_lean_dependencies as extract
    from . import generate_wiki as wiki
    from . import sync_wiki as sync
else:
    import extract_v2_lean_dependencies as extract
    import generate_wiki as wiki
    import sync_wiki as sync

OWN = "org.atlas-wiki"
AUTOFORM = "org.autoform"
SCHEMA = "atlas-cards/v1"
# The receipt of the moves command, which hooks/card_pages.py reads; and the links folder's defaults file (Autoform's
# annotations._DEFAULTS), which the receipt's digest of the annotations covers.
MOVES_SCHEMA = "atlas-card-moves/v2"
LINKS_DEFAULTS = "_defaults.json"
ARTICLE_ID = re.compile(r"af_[0-9a-f]{24}")
COMMIT = re.compile(r"[0-9a-f]{40}")
KINDS = ("concept", "result")
IMPORTANCE = ("landmark", "key", "supporting")
LEVELS = ("undergraduate", "graduate", "research")
RECORD_KEYS = {"kind", "main_article_id", "importance", "level", "supports", "seeds"}
REQUIRED = ("kind", "main_article_id", "importance", "level")
SEED_KEYS = {"source", "node", "revision"}
# The org.autoform keys a card's folder page may keep: presentation only.
FOLDER_KEYS = {"navigation", "area"}
# The declaration kinds lean-facts writes (a wanted declaration as the kind it stands for), by the card they can head.
CONCEPT_KINDS = frozenset({"def", "definition", "abbrev", "structure", "class", "inductive", "instance", "opaque",
                           "irreducible_def"})
RESULT_KINDS = frozenset({"theorem", "lemma", "proposition", "corollary"})
# Most statements a card holds: past it, `autoform audit` reports the folder (`overfull-container`, the graph
# rules' child limits).
MAX_LEAVES = 24
# Sections a card page never has: a card's edges are derived from its statements, never written by hand, and what a
# proof cites belongs to the statement it proves.
FORBIDDEN = ("depends on", "proof depends on", "informally uses")
# A Mathlib fact in a card's `## In Mathlib` list: its source line at the pinned Mathlib, titled with its name.
# Its path, raw: a plain module path, every segment letters, digits or `_` as all of Mathlib's are, so that no dot
# segment or percent-encoding can make a browser resolve it elsewhere than the commit it names.
MATHLIB_SOURCE = re.compile(r"/leanprover-community/mathlib4/blob/([0-9a-f]{40})/Mathlib(?:/[A-Za-z0-9_]+)*/[A-Za-z0-9_]+\.lean")
# The title of an `## In Mathlib` link must have the form of a Lean name: dot-separated parts, each an identifier
# (a letter or `_`, then letters, digits, `_`, primes `'`, `!`, `?` or subscripts) or a «quoted» one.
LEAN_PART = r"(?:[^\W\d][\w'!?\u2080-\u209c\u1d62-\u1d6a]*|«[^»]+»)"
LEAN_NAME = re.compile(rf"{LEAN_PART}(?:\.{LEAN_PART})*")
MOVES = "card-moves.jsonl"
# A planned page's counterparts (docs/cards.md#counterparts): each record names one declaration, of Mathlib or of
# the project, says how it compares with the page's statement, and may list the other declarations a combination
# takes.
LIBRARIES = ("mathlib", "atlas")
RELATIONS = ("same", "stronger", "weaker", "variant")
COUNTERPART_KEYS = {*LIBRARIES, "relation", "needs"}
# A statement's headline and its progress bucket: the first marker that applies, then Autoform's state key of a
# credited statement (`stated`: stated, its proof blocked; `planned`: blocked, not ready to state). A page-only
# statement is never shown as ready: with no declaration kind it is no task (the graph rules' planned pages and
# tasks), whatever state Autoform's index gives it.
MARKERS = ("stale", "held", "not_ready", "page_only")
STATES = ("mathlib", "fully_proved", "proved", "defined", "conditional", "can_prove", "stated", "can_state", "planned")
BUCKETS = MARKERS + STATES


def links_dir() -> Path:
    return wiki.VAULT / "links"


def moves_file() -> Path:
    return wiki.ROOT / "scripts" / MOVES


def node_id(page: Path) -> str:
    """Autoform's id of a roadmap page: its path below roadmap/ without `.md`; a folder page's is its folder's."""
    relative = page.relative_to(wiki.ROADMAP)
    if page.name == "README.md":
        return relative.parent.as_posix() if relative.parent.parts else "roadmap"
    return relative.with_suffix("").as_posix()


def statement_nodes(graph) -> dict[str, Path]:
    """Every statement page Autoform loaded, by node id, with its own file: a node whose file is not a folder page.
    A folder page shares its node id with a page of the same name beside it; the file says which one Autoform read."""
    return {node.id: Path(node.path).resolve() for node in graph.nodes.values() if Path(node.path).name != "README.md"}


def parse_rows(text: str) -> list[dict]:
    return sync.read_rows(text)


def by_page(rows_by_file: dict[str, list[dict]]) -> dict[Path, dict]:
    """Rows by the page each is about, as sync_wiki.subject_path reads it for extraction and the sync; a row Autoform
    leaves out is about no page (sync_wiki.credit_problems reports it)."""
    rows = {}
    for rows_of_file in rows_by_file.values():
        for annotation in rows_of_file:
            if (page := sync.subject_path(annotation)) is not None:
                rows[page] = annotation
    return rows


def read_annotations() -> dict[Path, dict]:
    """Every annotation of blueprint/links/*.jsonl in the checkout, by the page it names, as sync_wiki reads them."""
    return by_page({path.name: parse_rows(path.read_text()) for path in sorted(links_dir().glob("*.jsonl"))})


def committed_annotations() -> dict[Path, dict] | None:
    """The annotations as committed at HEAD, or None outside a Git checkout."""
    try:
        root = Path(subprocess.run(["git", "-C", str(wiki.ROOT), "rev-parse", "--show-toplevel"], check=True,
                                   capture_output=True, text=True).stdout.strip()).resolve()
    except (OSError, subprocess.CalledProcessError):
        return None
    if root != wiki.ROOT.resolve():
        return None
    files = {}
    for path in sorted(links_dir().glob("*.jsonl")):
        relative = path.resolve().relative_to(root).as_posix()
        shown = subprocess.run(["git", "-C", str(root), "show", f"HEAD:{relative}"], capture_output=True, text=True)
        if shown.returncode == 0:
            files[path.name] = parse_rows(shown.stdout)
    return by_page(files)


def source_commit() -> str | None:
    try:
        return subprocess.run(["git", "-C", str(wiki.ROOT), "rev-parse", "HEAD"], check=True, capture_output=True,
                              text=True).stdout.strip() or None
    except (OSError, subprocess.CalledProcessError):
        return None


def legacy(annotation: dict | None) -> tuple[str, str] | None:
    """The module and name of a row an earlier sync wrote without a Lean link (sync_wiki.legacy_pair, the one test of
    such a row). lean-facts resolves it through the Lean index and gives the build's row the Lean link of the one
    declaration it finds; the cards read that link, and never resolve such a row themselves."""
    return sync.legacy_pair(annotation)


def credit(annotation: dict | None) -> str:
    """Whom a row credits, by sync_wiki.page_owner: `mathlib` for a Mathlib-credited row (a flagged row whose
    credit is ambiguous counts too, and check reports it), `atlas` for a declaration of the project (or a row an
    earlier sync wrote with a module and a name, which credits a declaration once lean-facts gives it that
    declaration's Lean link, and is stale otherwise), else `none`."""
    if annotation is None:
        return "none"
    try:
        owner = sync.page_owner(annotation)[0]
    except sync.CreditError:
        return "mathlib"
    if owner != "none":
        return owner
    return "atlas" if legacy(annotation) else "none"


def declaration(annotation: dict | None) -> str | None:
    """The declaration a row credits, by sync_wiki.page_owner: its Mathlib declaration, or its project declaration."""
    if annotation is None:
        return None
    try:
        return sync.page_owner(annotation)[1]
    except sync.CreditError:
        return None


@dataclass
class Page:
    """A Markdown page as Autoform reads it: fenced blocks, indented code and HTML comments are blanked first (by
    Autoform's own masking), so a heading, a link or a list item inside one does not count, and a heading reads
    without its comments (`## Depends <!-- note -->on` is `## Depends on`)."""

    title: str | None
    opening: str
    frontmatter: bool
    sections: dict[str, list[str]] = field(default_factory=dict)
    headings: list[str] = field(default_factory=list)


def read_page(text: str) -> Page:
    from autoform_cli import markdown

    lines = text.splitlines()
    start = markdown.frontmatter_end(lines)
    masked = markdown.mask_code_and_comments(lines[start:])
    title, opening, sections, headings = None, [], {}, []
    current: list[str] | None = None
    for line in masked:
        match = markdown.HEADING.match(line)
        level = len(match.group(1)) if match else 0
        if level == 2:
            heading = " ".join(match.group(2).split())
            headings.append(heading)
            current = sections.setdefault(heading.casefold(), [])
            continue
        if level == 1 and title is None and current is None:
            title = " ".join(match.group(2).split())
            continue
        (opening if current is None else current).append(line)
    return Page(title, "\n".join(opening), start > 0, sections, headings)


@dataclass
class Shown:
    """What a reader sees of one part of a page as the site renders it: its text, each top-level list item's first
    link (destination and label; None and "" for an item with no link) and whether the item's first visible content
    is that link, and every link a reader can follow (destination, label, title)."""

    text: str = ""
    items: list[tuple[str | None, str, bool]] = field(default_factory=list)
    links: list[tuple[str, str, str | None]] = field(default_factory=list)


@dataclass
class PageView:
    """A page as the site publishes and renders it: None when Autoform's publication check would show it as typed
    text; else its title (the first `<h1>`), its opening (what comes before the first `<h2>`) and its sections, by
    the casefolded text of their `<h2>`."""

    title: str
    opening: Shown
    sections: dict[str, Shown]
    #: The `<h2>` texts the page shows more than once.
    repeated: list[str] = field(default_factory=list)
    #: The targets of the links in its title and its `<h2>`s, which are no section's text.
    heading_links: list[str] = field(default_factory=list)


# Elements a reader is not shown at all; code is shown, as code.
UNSHOWN = sync.HIDDEN - {"code", "pre"}


def page_view(text: str) -> PageView | None:
    """The whole page rendered as the site renders it (sync_wiki.published, then sync_wiki.renderer and the tree a
    browser builds), so that a reference link defined anywhere on the page counts, then cut at its `<h2>`s."""
    import html5lib

    shown = sync.published(text)
    if shown is None:
        return None
    md = sync.renderer()
    md.reset()
    tree = html5lib.HTMLParser(namespaceHTMLElements=False).parse(md.convert(shown), scripting=True)
    body = tree.find("body")
    body = tree if body is None else body

    def hidden(node, child) -> bool:
        tag = child.tag if isinstance(child.tag, str) else ""
        return (tag in UNSHOWN or "hidden" in child.attrib
                or bool(re.search(r"display\s*:\s*none|visibility\s*:\s*hidden", child.get("style", ""), re.I))
                or tag == "dialog" and "open" not in child.attrib
                or node.tag == "details" and "open" not in node.attrib and tag != "summary")

    def words(node) -> str:
        return " ".join("".join(node.itertext()).split())

    def first_shown(node, chain: list) -> list | None:
        """The chain of elements down to the one whose text a reader sees first in ``node``."""
        if node.text and node.text.strip():
            return [*chain, node]
        for child in node:
            if not hidden(node, child):
                if (found := first_shown(child, [*chain, node])) is not None:
                    return found
            if child.tail and child.tail.strip():
                return [*chain, node]
        return None

    def collect(element, part: Shown, texts: list[str], in_item: bool) -> None:
        if element.tag == "a" and element.get("href") is not None:
            part.links.append((element.get("href"), words(element), element.get("title")))
        if element.tag == "li" and not in_item:
            link = next((a for a in element.iter("a") if a.get("href") is not None), None)
            chain = first_shown(element, []) or []
            part.items.append((None if link is None else link.get("href"), "" if link is None else words(link),
                               link is not None and link in chain))
            in_item = True
        if element.text:
            texts.append(element.text)
        for child in element:
            if not hidden(element, child):
                collect(child, part, texts, in_item)
            if child.tail:
                texts.append(child.tail)

    title, opening, sections, repeated, heading_links = "", Shown(), {}, [], []
    current, texts = opening, []
    parts: list[tuple[Shown, list[str]]] = [(opening, texts)]
    for child in body:
        tag = child.tag if isinstance(child.tag, str) else ""
        if tag in ("h1", "h2"):
            heading_links += [a.get("href") for a in child.iter("a") if a.get("href") is not None]
        if tag == "h1" and not title and current is opening:
            title = words(child)
        elif tag == "h2":
            current, texts = Shown(), []
            key = words(child).casefold()
            if key in sections:
                repeated.append(words(child))
            sections.setdefault(key, current)
            parts.append((current, texts))
        elif not hidden(body, child):
            collect(child, current, texts, False)
        if child.tail:
            texts.append(child.tail)
    for part, part_texts in parts:
        part.text = " ".join("".join(part_texts).split())
    return PageView(title, opening, sections, repeated, heading_links)


def mathlib_source(href: str) -> str | None:
    """The Mathlib commit of a link to a source line, `https://github.com/leanprover-community/mathlib4/blob/<commit>/
    Mathlib/<path>.lean#L<line>` with no query and nothing else in its fragment; None for any other link."""
    try:
        split = urlsplit(href)
    except ValueError:
        return None
    if split.scheme != "https" or split.netloc != "github.com" or split.query:
        return None
    match = MATHLIB_SOURCE.fullmatch(split.path)
    return match.group(1) if match is not None and re.fullmatch(r"L\d+", split.fragment) else None


def link_target(folder: Path, href: str) -> Path | None:
    """The file a relative link on a page of ``folder`` leads to, by its percent-decoded URL path (no query or
    fragment); a folder stands for its folder page, as the site serves it; None for a link with a scheme or a
    host, or one to the page itself."""
    try:
        split = urlsplit(href)
    except ValueError:
        return None
    path = unquote(split.path)
    if split.scheme or split.netloc or not path:
        return None
    target = (folder / path).resolve()
    return target / "README.md" if path.endswith("/") or target.is_dir() else target


def mathlib_pin() -> str | None:
    """The Mathlib commit lake-manifest.json pins."""
    path = wiki.ROOT / "lake-manifest.json"
    if not path.is_file():
        return None
    return next((package.get("rev") for package in json.loads(path.read_text()).get("packages", [])
                 if package.get("name", "").lower() == "mathlib"), None)


@dataclass
class Card:
    id: str | None
    folder: Path
    record: object
    annotation: dict

    @property
    def node(self) -> str:
        return node_id(self.folder / "README.md")


def misplaced_records(annotations: dict[Path, dict]) -> list[str]:
    """A card record on a statement page, or an `org.atlas-wiki` extension that is not an object: the card would
    silently not exist."""
    errors = []
    for page, annotation in sorted(annotations.items()):
        own = annotation.get("extensions", {}).get(OWN)
        if own is None:
            continue
        if not isinstance(own, dict):
            errors.append(f"{node_id(page)}: its `{OWN}` extension is not an object")
        elif "card" in own and page.name != "README.md":
            errors.append(f"{node_id(page)}: a card record belongs on a folder page, not on a statement page")
    return errors


def lean_linked(annotation: dict | None) -> bool:
    """Whether a row links a Lean declaration, as Autoform reads it over the folder defaults: a Lean end naming a
    declaration, of this project, of Mathlib or of another one, or the module and name an earlier sync wrote, which
    lean-facts reads as a link. A statement page whose row links none is planned."""
    if not isinstance(annotation, dict):
        return False
    read = sync.effective(annotation) or annotation
    objects = read.get("object", [])
    return sync.legacy_pair(annotation) is not None or any(
        isinstance(end, dict) and end.get("type") == "lean" and isinstance(end.get("location"), dict)
        and end["location"].get("declaration") is not None for end in (objects if isinstance(objects, list) else []))


def name_components(name: str) -> tuple[str, ...]:
    """A Lean name's components as Lean reads them, each without the «» that may quote it: `Matrix.«det»` and
    `Matrix.det` are one name, while `«a.b».c`, two components, is not `a.b.c`, three. *name* has the form
    LEAN_NAME gives."""
    return tuple(part[1:-1] if part.startswith("«") else part for part in re.findall(LEAN_PART, name))


def spelled(first: str, second: str) -> str:
    """How a problem shows a second spelling of a name it has shown as *first*: nothing when they are the same."""
    return "" if first == second else f" (once as {second})"


def named(entry: dict, what: str) -> tuple[tuple[str, str] | None, list[str]]:
    """The library and name of the one declaration *entry* names (exactly one of `mathlib` and `atlas`, a Lean
    name), and what is wrong with it."""
    libraries = [library for library in LIBRARIES if library in entry]
    if len(libraries) != 1:
        given = "no declaration" if not libraries else "two declarations"
        return None, [f"{what} names {given}; give exactly one of `mathlib` and `atlas`"]
    library = libraries[0]
    name = entry[library]
    if not (isinstance(name, str) and LEAN_NAME.fullmatch(name)):
        return None, [f"{what}: `{library}` is {name!r}, not a Lean name"]
    if name_components(name)[0] == "_root_":
        return None, [f"{what}: `{library}` is {name!r}; write the full name without `_root_.`, a prefix only Lean "
                      "source writes, never part of a declaration's name"]
    return (library, name), []


def counterpart_shape(value: object) -> list[str]:
    """What is wrong with the form of a `counterpart` list: a non-empty list of records, each naming exactly one
    declaration (`mathlib` or `atlas`, a Lean name), with its `relation` and an optional non-empty `needs` list of
    such declarations, each `{"mathlib": name}` or `{"atlas": name}`, and no other key; no declaration twice in a
    list, and a record's own declaration not among its needs, a declaration being its library and its name as Lean
    reads it (name_components), whatever the spelling."""
    if not isinstance(value, list) or not value:
        return ["`counterpart` must be a non-empty list of records"]
    problems: list[str] = []
    recorded: dict[tuple[str, tuple[str, ...]], str] = {}
    for number, record in enumerate(value, 1):
        what = f"`counterpart` record {number}"
        if not isinstance(record, dict):
            problems.append(f"{what} is not an object")
            continue
        problems += [f"{what} has the unknown key `{key}`" for key in sorted(set(record) - COUNTERPART_KEYS)]
        target, found = named(record, what)
        problems += found
        if "relation" not in record:
            problems.append(f"{what} has no `relation`; give one of {', '.join(RELATIONS)}")
        elif record["relation"] not in RELATIONS:
            problems.append(f"{what}: `relation` is {record['relation']!r}; expected one of {', '.join(RELATIONS)}")
        own = None if target is None else (target[0], name_components(target[1]))
        if own is not None:
            if own in recorded:
                first = recorded[own]
                problems.append(f"`counterpart` names {target[0]} {first} twice{spelled(first, target[1])}")
            else:
                recorded[own] = target[1]
        if "needs" not in record:
            continue
        needs = record["needs"]
        if not isinstance(needs, list) or not needs:
            problems.append(f'{what}: `needs` must be a non-empty list of declarations, each {{"mathlib": name}} or '
                            '{"atlas": name}; leave it out when the declaration needs no other')
            continue
        listed: dict[tuple[str, tuple[str, ...]], str] = {}
        for index, entry in enumerate(needs, 1):
            where = f"{what}, `needs` entry {index}"
            if not isinstance(entry, dict):
                problems.append(f"{where} is not an object naming one declaration")
                continue
            problems += [f"{where} has the unknown key `{key}`" for key in sorted(set(entry) - set(LIBRARIES))]
            other, found = named(entry, where)
            problems += found
            if other is None:
                continue
            key = (other[0], name_components(other[1]))
            if key in listed:
                problems.append(f"{what}: `needs` names {other[0]} {listed[key]} twice{spelled(listed[key], other[1])}")
                continue
            if key == own:
                shown = "" if other[1] == target[1] else f" (as {other[1]})"
                problems.append(f"{what}: `needs` names the record's own declaration, {target[0]} {target[1]}{shown}")
            listed[key] = other[1]
    return problems


def counterpart_keys(value: object, path: str) -> list[str]:
    """Where a `counterpart` key sits in *value*, at any depth, in an object or a list, each as a path from *path*."""
    found = []
    if isinstance(value, dict):
        for key, inner in value.items():
            here = f"{path}[{json.dumps(key, ensure_ascii=False)}]"
            found += [here] if key == "counterpart" else counterpart_keys(inner, here)
    elif isinstance(value, list):
        for index, inner in enumerate(value):
            found += counterpart_keys(inner, f"{path}[{index}]")
    return found


def counterpart_pages(annotations: dict[Path, dict]) -> list[Path]:
    """The rows' pages that record a counterpart."""
    return sorted(page for page, annotation in annotations.items()
                  if isinstance(own := (annotation.get("extensions") or {}).get(OWN), dict) and "counterpart" in own)


def counterpart_problems(annotations: dict[Path, dict], committed: dict[Path, dict]) -> list[str]:
    """What is wrong with the counterparts the rows record (docs/cards.md#counterparts): a counterpart belongs to a
    planned statement page, one whose row links no Lean declaration (lean_linked), as checked out and as committed,
    since lean-facts may drop a committed link; it has the form counterpart_shape gives; and the links folder's
    defaults give none, anywhere under their `org.atlas-wiki` extension, a card record included, as they would give
    it to every row, a credited or a folder page's included (counterpart_keys). Only the form
    is checked: that a record is true is for review. A card record that holds one is check_record's, and a row whose
    page Autoform does not read, check's, which has Autoform's graph (live_counterparts)."""
    errors = []
    template = sync.links_template()
    inherited = template.get("extensions") if isinstance(template, dict) else None
    folder = sync.LINKS.relative_to(wiki.ROOT).as_posix() if sync.LINKS.is_relative_to(wiki.ROOT) else sync.LINKS
    for path in counterpart_keys(inherited.get(OWN) if isinstance(inherited, dict) else None, f'extensions["{OWN}"]'):
        errors.append(f"{folder}/_defaults.json sets `counterpart` at `{path}`, which would give every row that "
                      "counterpart; a counterpart belongs on a planned statement page's own row: remove it from the "
                      "defaults")
    for page, annotation in sorted(annotations.items()):
        extensions = annotation.get("extensions")
        own = extensions.get(OWN) if isinstance(extensions, dict) else None
        if not isinstance(own, dict) or "counterpart" not in own:
            continue  # an `org.atlas-wiki` extension that is no object is misplaced_records'
        where = node_id(page)
        if page.name == "README.md":
            errors.append(f"{where}: a counterpart belongs on a planned statement page, not on a folder page")
            continue
        if lean_linked(annotation) or lean_linked(committed.get(page)):
            errors.append(f"{where}: a counterpart belongs on a planned page, whose annotation links no Lean "
                          "declaration; this one links one")
        errors += [f"{where}: {problem}" for problem in counterpart_shape(own["counterpart"])]
    return errors


def live_counterparts(annotations: dict[Path, dict], graph) -> list[str]:
    """A counterpart on a row whose page is no live statement page Autoform reads, under its node id: its file is
    missing (an orphan row), or Autoform's loader passes it over (a hidden page, say)."""
    errors = []
    read = statement_nodes(graph)
    for page in counterpart_pages(annotations):
        if page.name == "README.md":
            continue  # counterpart_problems reports it
        if not page.is_file():
            errors.append(f"{node_id(page)}: a counterpart belongs on a statement page Autoform reads; its page is "
                          "missing")
        elif read.get(node_id(page)) != page.resolve():
            shown = page.resolve().relative_to(wiki.ROADMAP.resolve()).as_posix()
            errors.append(f"{node_id(page)}: a counterpart belongs on a statement page Autoform reads; Autoform does "
                          f"not read {shown} as one")
    return errors


def card_folders(annotations: dict[Path, dict]) -> dict[Path, Card]:
    """Every card, by its folder: a folder page whose annotation carries a card record."""
    cards = {}
    for page, annotation in annotations.items():
        own = annotation.get("extensions", {}).get(OWN, {})
        if page.name == "README.md" and isinstance(own, dict) and "card" in own:
            cards[page.parent] = Card(annotation.get("id"), page.parent, own["card"], annotation)
    return dict(sorted(cards.items()))


def structural(folder: Path) -> str | None:
    """What the wiki's structure makes of a folder that is no topic: a subject, a field, a subfield of the taxonomy
    (scripts/taxonomy.json), or a part folder the generator adds to split a long list; None for a topic folder or
    a folder inside one."""
    parts = folder.relative_to(wiki.ROADMAP).parts
    if len(parts) < 3:
        return "a subject or a field"
    if re.fullmatch(r"part-\d+", parts[-1]):
        return "a part folder the generator adds to split a long list"
    if len(parts) == 3:
        path = wiki.ROOT / "scripts" / "taxonomy.json"
        taxonomy = json.loads(path.read_text()) if path.is_file() else {}
        fields = taxonomy.get("subjects", {}).get(parts[0], {}).get("fields", [])
        for field_spec in fields if isinstance(fields, list) else []:
            if isinstance(field_spec, dict) and field_spec.get("slug") == parts[1]:
                subfields = {sub.get("slug") if isinstance(sub, dict) else sub for sub in field_spec.get("subfields", [])}
                if parts[2] in subfields:
                    return "a subfield"
    return None


def leaves(folder: Path) -> list[Path]:
    return sorted(path for path in folder.glob("*.md") if path.name != "README.md")


def subfolders(folder: Path) -> list[Path]:
    return sorted(path for path in folder.iterdir() if path.is_dir() and (path / "README.md").is_file())


def valid_seed(seed: object) -> bool:
    return (isinstance(seed, dict) and set(seed) == SEED_KEYS and all(isinstance(v, str) and v for v in seed.values())
            and COMMIT.fullmatch(seed["revision"]) is not None)


def check_record(card: Card, by_id: dict[str, Path], annotations: dict[Path, dict]) -> tuple[list[str], Path | None]:
    """The errors of one card's record and annotation, and its main statement's page when the record names one."""
    errors: list[str] = []
    record = card.record
    if not isinstance(record, dict):
        return ["the card record is not an object"], None
    errors += [f"unknown card key `{key}`" for key in sorted(set(record) - RECORD_KEYS - {"counterpart"})]
    if "counterpart" in record:
        errors.append("a card records no counterpart; a counterpart belongs on a planned statement page's "
                      "annotation (docs/cards.md#counterparts)")
    errors += [f"the card record has no `{key}`" for key in REQUIRED if key not in record]
    for key, allowed in (("kind", KINDS), ("importance", IMPORTANCE), ("level", LEVELS)):
        if key in record and record[key] not in allowed:
            errors.append(f"`{key}` is {record[key]!r}; expected one of {', '.join(allowed)}")
    if not (isinstance(card.id, str) and ARTICLE_ID.fullmatch(card.id)):
        errors.append("the card's annotation needs an `id`, `af_` and 24 lowercase hex digits (docs/BLUEPRINT.md, "
                      "What the tools own)")
    for key in ("object", "kind", "status"):
        if key in card.annotation:
            errors.append(f"a card credits no declaration, so its annotation has no `{key}`")
    extensions = card.annotation.get("extensions", {})
    for key in sorted(set(extensions.get(AUTOFORM, {})) - FOLDER_KEYS):
        errors.append(f"a card credits no declaration, so its annotation has no `{AUTOFORM}` key `{key}`")
    if "held" in extensions.get(OWN, {}):
        errors.append("a card credits no declaration, so its annotation holds none back")
    for key in ("module", "name"):
        if key in extensions.get(OWN, {}):
            errors.append(f"a card credits no declaration, so its annotation has no `{OWN}` key `{key}` (an earlier "
                          "sync's declaration credit)")
    main = record.get("main_article_id")
    main_page = None
    if "main_article_id" in record:
        if not (isinstance(main, str) and ARTICLE_ID.fullmatch(main)):
            errors.append(f"`main_article_id` is {main!r}; expected an article id")
        elif main not in by_id:
            errors.append(f"`main_article_id` {main} is no annotation's id")
        elif by_id[main].name == "README.md" or by_id[main].parent != card.folder:
            errors.append(f"`main_article_id` {main} is {node_id(by_id[main])}, not a statement page of this folder")
        else:
            main_page = by_id[main]
    supports = record.get("supports", [])
    if not isinstance(supports, list):
        errors.append("`supports` is not a list")
        supports = []
    if len({json.dumps(other) for other in supports}) != len(supports):
        errors.append("`supports` names a statement twice")
    for other in supports:
        if not (isinstance(other, str) and ARTICLE_ID.fullmatch(other)) or other not in by_id:
            errors.append(f"`supports` names {other!r}, which is no annotation's id")
        elif by_id[other].name == "README.md":
            errors.append(f"`supports` names {node_id(by_id[other])}, a folder page")
        elif not by_id[other].is_file():
            errors.append(f"`supports` names {other}, whose page {node_id(by_id[other])} is missing")
        elif by_id[other].parent == card.folder:
            errors.append(f"`supports` names {node_id(by_id[other])}, a statement of this card")
    seeds = record.get("seeds", [])
    if not isinstance(seeds, list) or not all(valid_seed(seed) for seed in seeds):
        errors.append("`seeds` must be a list of objects with exactly `source`, `node` and `revision` (a full commit)")
    return errors, main_page


def check(annotations: dict[Path, dict] | None = None, graph=None, committed: dict[Path, dict] | None = None,
          dependencies: dict | None = None, base_ledger: str | None = None,
          base_annotations: dict[Path, dict] | None = None, renames: list[tuple[str, str]] | None = None,
          registry: dict | None = None) -> tuple[list[str], list[str]]:
    """The errors and the warnings about every card and the move ledger. ``graph`` is Autoform's graph of the
    checkout (loaded here when None and there are cards or ``dependencies``); ``committed`` the committed
    annotations (the checkout's when None); ``dependencies`` an extraction every credited page's dependencies must
    come from (the strict check, which also needs the ledger); ``base_ledger`` the ledger the base commit published,
    which must stay a prefix; ``base_annotations`` the base commit's rows, against which every changed address needs
    its ledger row; ``registry`` the build's Mathlib registry."""
    # A registry is read only once its form is the extractor's: a table of another type would otherwise stop the
    # check with a traceback rather than an error.
    if registry is not None and (problems := sync.registry_form_problems(registry)):
        return problems, []
    annotations = read_annotations() if annotations is None else annotations
    committed = annotations if committed is None else committed
    cards = card_folders(annotations)
    by_id = {annotation["id"]: page for page, annotation in annotations.items() if isinstance(annotation.get("id"), str)}
    # Each card's main statement, as its record names it (check_record says when that is wrong).
    main_pages = {folder: by_id.get(card.record.get("main_article_id")) for folder, card in cards.items()
                  if isinstance(card.record, dict) and isinstance(card.record.get("main_article_id"), str)}
    # No credit overrides a held marker (sync_wiki.held_conflicts, as the extraction and lean-facts refuse it).
    errors: list[str] = misplaced_records(annotations) + counterpart_problems(annotations, committed)
    errors += sync.held_conflicts({Path("links"): list(annotations.values())})
    warnings: list[str] = []
    mains: dict[Path, str] = {}
    teaching: dict[Path, list[Path]] = {}
    for folder, card in cards.items():
        where = card.node
        found, main_page = check_record(card, by_id, annotations)
        errors += [f"{where}: {message}" for message in found]
        if main_page is not None:
            if main_page in mains:
                errors.append(f"{where}: its main statement already heads {mains[main_page]}")
            mains[main_page] = where
        if (structure := structural(folder)) is not None:
            errors.append(f"{where}: a card is a topic folder or a folder inside one, never {structure}")
        for inner in subfolders(folder):
            errors.append(f"{where}: a card holds statement pages only, not the folder {node_id(inner / 'README.md')}")
        members = leaves(folder)
        if not members:
            errors.append(f"{where}: a card holds at least its main statement")
        if len(members) > MAX_LEAVES:
            errors.append(f"{where}: {len(members)} statements; a card holds at most {MAX_LEAVES} (Autoform's child "
                          "limit)")
        for member in members:
            seed = annotations.get(member, {}).get("extensions", {}).get(OWN, {}).get("seed")
            if seed is not None and not valid_seed(seed):
                errors.append(f"{node_id(member)}: its `seed` needs exactly `source`, `node` and `revision` (a full "
                              "commit)")
        record = card.record if isinstance(card.record, dict) else {}
        if main_page is not None and record.get("kind") in KINDS:
            own, authored = annotations.get(main_page, {}), credit(committed.get(main_page))
            kind = own.get("kind")
            if authored == "mathlib" and credit(own) == "mathlib":
                # Mathlib's own classification of the declaration, from the registry, decides.
                found = (registry or {}).get("mathlib", {}).get(declaration(own) or "")
                if found is None and kind is not None:
                    # Without the registry, a kind lean-facts gave still has to fit, as for an ATLAS main.
                    allowed = CONCEPT_KINDS if record["kind"] == "concept" else RESULT_KINDS
                    if kind not in allowed:
                        errors.append(f"{where}: a {record['kind']} card's main statement {node_id(main_page)} is a "
                                      f"`{kind}`")
                elif found is None:
                    warnings.append(f"{where}: the kind of the Mathlib main statement {node_id(main_page)} is unknown "
                                    "without the build's registry")
                elif not isinstance(found.get("proposition"), bool):
                    errors.append(f"{where}: the registry does not say whether the Mathlib main statement "
                                  f"{declaration(own)} states a proposition")
                elif found["proposition"] is not (record["kind"] == "result"):
                    what = "states a proposition" if found["proposition"] else "does not state a proposition"
                    errors.append(f"{where}: a {record['kind']} card's main statement {node_id(main_page)} is "
                                  f"Mathlib's {declaration(own)}, which {what}")
            elif kind is not None:
                # A credited main's kind, or the one lean-facts gives a main with no Lean link that counts as a
                # statement not yet in Lean (held, or recording its kind), fits the card.
                allowed = CONCEPT_KINDS if record["kind"] == "concept" else RESULT_KINDS
                if kind not in allowed:
                    errors.append(f"{where}: a {record['kind']} card's main statement {node_id(main_page)} is a `{kind}`")
            elif authored == "atlas" and credit(own) == "atlas":
                warnings.append(f"{where}: the kind of the main statement {node_id(main_page)} is unknown; run after "
                                "sync_wiki.py lean-facts")
        readme = folder / "README.md"
        if not readme.is_file():
            errors.append(f"{where}: the card's folder page is missing")
            continue
        text = readme.read_text()
        page = read_page(text)
        view = page_view(text)
        if page.frontmatter:
            errors.append(f"{where}: a card's page has no frontmatter; its facts are in its annotation")
        for heading in page.headings:
            if heading.casefold() in FORBIDDEN:
                errors.append(f"{where}: a card's page has no `## {heading}`: its edges come from its statements")
        if view is None:
            errors.append(f"{where}: Autoform would publish the card's page as typed, with no live link or heading "
                          "(raw HTML, say); write it in plain Markdown")
            continue
        for heading in view.repeated:
            errors.append(f"{where}: the card's page has two `## {heading}` sections; each section is written once")
        if not view.title:
            errors.append(f"{where}: the card's page has no title")
        if not view.opening.text:
            errors.append(f"{where}: the card's page opens with no statement or summary before its first section")
        if not view.sections.get("idea", Shown()).text:
            errors.append(f"{where}: the card's page needs an `## Idea` section that explains it to a learner")
        if "statements" not in view.sections:
            errors.append(f"{where}: the card's page needs a `## Statements` section listing its statement pages")
        else:
            items = view.sections["statements"].items
            if any(href is None or not opens for href, _, opens in items):
                errors.append(f"{where}: an item of `## Statements` does not open with a link to a statement page")
            if any(href is not None and not label for href, label, _ in items):
                errors.append(f"{where}: a link of `## Statements` has no text a reader can see")
            listed = [PurePosixPath(href.split("#")[0]).as_posix().removeprefix("./")
                      for href, _, _ in items if href is not None]
            names = [member.name for member in members]
            for name, count in sorted(Counter(listed).items()):
                if count > 1:
                    errors.append(f"{where}: `## Statements` lists {name} {count} times")
                if name not in names:
                    errors.append(f"{where}: `## Statements` lists {name}, which is not a statement page of this card")
            for name in names:
                if name not in listed:
                    errors.append(f"{where}: `## Statements` does not list {name}")
            # Every other link of the section to a statement page, in prose or a nested list, counts too: each of the
            # card's pages is linked there once, and no other statement page is.
            firsts = Counter(href for href, _, _ in items if href is not None)
            for href, _, _ in view.sections["statements"].links:
                if firsts[href] > 0:
                    firsts[href] -= 1
                    continue
                split = urlsplit(href) if href else None
                local = split is not None and not split.scheme and not split.netloc
                page = (folder / "README.md" if local and not split.path else link_target(folder, href)) if local \
                    else None
                leaf = page.parent / f"{unquote(split.fragment)}.md" if page is not None and split.fragment else None
                # Autoform boxes a leaf on its folder page when it declares something (a declaration kind) or is a
                # module catalog; a page-only leaf has a page of its own, and the anchor is then a heading's.
                boxed = leaf is not None and page.name == "README.md" and leaf.is_file() and (
                    "kind" in annotations.get(leaf.resolve(), {})
                    or "catalog" in annotations.get(leaf.resolve(), {}).get("extensions", {}).get(AUTOFORM, {}))
                if boxed:
                    # A statement's box on a folder page (`#leaf`, `../other/README.md#leaf`) is that statement by
                    # another route; an ordinary heading anchor is not.
                    errors.append(f"{where}: `## Statements` links {href}, a statement's box on a folder page; a "
                                  "statement is linked there by its own page")
                    continue
                target = link_target(folder, href) if href else None
                if target is None or target.suffix != ".md" or target.name == "README.md":
                    continue
                if target.parent == folder and target.name in names:
                    errors.append(f"{where}: `## Statements` links {target.name} again, after its item; each of the "
                                  "card's pages is linked there once")
                else:
                    errors.append(f"{where}: `## Statements` links {href}, which is not a statement page of this card")
            if main_page is not None and listed and listed[0] != main_page.name:
                errors.append(f"{where}: `## Statements` lists {listed[0]} first, not the main statement "
                              f"{main_page.name}")
        teaching[folder] = []
        for target, _, _ in view.sections.get("background", Shown()).links:
            linked = link_target(folder, target)
            if linked is not None and linked.name == "README.md" and linked.parent == folder:
                warnings.append(f"{where}: `## Background` links the card itself; it lists other cards to know first")
            elif linked is not None and linked.name == "README.md" and linked.parent in cards:
                teaching[folder].append(linked.parent)
            else:
                warnings.append(f"{where}: `## Background` links {target}, which is not a card's page")
        # A card links another card only under `## Background` (the graph rules' Cards); elsewhere it links its main
        # statement.
        outside = [("its opening", [href for href, _, _ in view.opening.links]),
                   ("a heading", view.heading_links)] + [
            (f"`## {name[:1].upper()}{name[1:]}`", [href for href, _, _ in part.links])
            for name, part in view.sections.items() if name != "background"]
        for part_name, targets in outside:
            for target in targets:
                linked = link_target(folder, target) if target else None
                if linked is not None and linked.name == "README.md" and linked.parent in cards and \
                        linked.parent != folder:
                    errors.append(f"{where}: {part_name} links the card {node_id(linked)}; a card links another card "
                                  "only under `## Background`, and elsewhere its main statement")
                elif linked is not None and linked.suffix == ".md" and linked.name != "README.md" and \
                        linked.parent in cards and linked.parent != folder and main_pages.get(linked.parent) != linked \
                        and part_name != "`## Statements`":
                    errors.append(f"{where}: {part_name} links {node_id(linked)}, a statement of the card "
                                  f"{node_id(linked.parent / 'README.md')} that is not its main statement; outside "
                                  "`## Background` a card links another card only through its main statement")
    for cycle in cycles(teaching):
        warnings.append("`## Background` links go round: " + " -> ".join(node_id(path / "README.md") for path in cycle))
    errors += check_moves(annotations, cards, base_ledger, dependencies is not None, base_annotations, renames)
    pin = mathlib_pin()
    for folder, card in cards.items():
        readme = folder / "README.md"
        if not readme.is_file():
            continue
        shown = page_view(readme.read_text())
        for href, label, title in (shown.sections.get("in mathlib", Shown()).links if shown is not None else []):
            source = mathlib_source(href) if href else None
            if source is None or not title or not label or not LEAN_NAME.fullmatch(title):
                errors.append(f"{card.node}: `## In Mathlib` links {href}; a Mathlib fact links its source line at the "
                              "pinned Mathlib, titled with the declaration's Lean name")
            elif pin is not None and source != pin:
                errors.append(f"{card.node}: `## In Mathlib` links Mathlib {source}, not the pinned {pin}")
    if graph is None and (cards or dependencies is not None or counterpart_pages(annotations)):
        try:
            graph = load_graph()
        except Exception as error:  # Autoform refuses the wiki, e.g. two articles on one address.
            return errors + [f"Autoform cannot load the wiki: {error}"], warnings
    if graph is not None:
        errors += live_counterparts(annotations, graph)
    if graph is not None and cards:
        nodes = {card.node for card in cards.values()}
        # A `supports` entry names a statement page Autoform reads: that very file, under its node id.
        read = statement_nodes(graph)
        for card in cards.values():
            if not isinstance(card.record, dict):
                continue  # check_record has reported it
            for other in card.record.get("supports", []) if isinstance(card.record.get("supports"), list) else []:
                page = by_id.get(other) if isinstance(other, str) else None
                if page is not None and page.is_file() and page.name != "README.md" and \
                        read.get(node_id(page)) != page.resolve():
                    shown = page.resolve().relative_to(wiki.ROADMAP.resolve()).as_posix()
                    errors.append(f"{card.node}: `supports` names {other}, whose file {shown} is no statement page "
                                  "Autoform reads")
        for card in cards.values():
            node = graph.nodes.get(card.node)
            if node is not None and (node.statement_dependencies or node.proof_dependencies
                                     or node.informal_dependencies):
                errors.append(f"{card.node}: Autoform reads dependencies on the card's page; its edges come from its "
                              "statements")
        for node in sorted(graph.nodes.values(), key=lambda node: node.id):
            for kind, targets in (("statement", node.statement_dependencies), ("proof", node.proof_dependencies)):
                for target in targets:
                    if target in nodes:
                        errors.append(f"{node.id}: its {kind} depends on the card {target}; a dependency names a "
                                      "statement, and a card is a folder of them")
            for target in node.informal_dependencies:
                if target in nodes:
                    warnings.append(f"{node.id}: `## Informally uses` links the card {target}, not a statement")
    if graph is not None and dependencies is not None:
        errors += integrity(graph, annotations, dependencies, registry)
        resolved = resolved_names(graph, annotations, dependencies)
        # The declarations the pages stand for, a row an earlier sync wrote with a module and a name included once
        # lean-facts gave it its Lean link.
        errors += mathlib_credit_problems(graph, annotations, committed, registry, set(resolved.values()))
        # A declaration has one page, whatever names it (sync_wiki.owner_problems has the Lean index for the same check
        # before lean-facts writes); a page whose committed row has only a module and a name is labelled so.
        standing: dict[str, dict[str, bool]] = defaultdict(dict)
        files = statement_nodes(graph)
        for path, name in sorted(resolved.items()):
            authored = committed.get(files[path])
            standing[name][path] = legacy(authored) is not None and declaration(authored) is None
        errors += [sync.shared_owner(name, paths) for name, paths in sorted(standing.items()) if len(paths) > 1]
        for page, annotation in sorted(annotations.items()):
            path = node_id(page)
            if (page.name != "README.md" and path in graph.nodes and legacy(annotation) is not None
                    and path not in resolved):
                warnings.append(f"{path}: its module-and-name row names no declaration the Lean index resolves, so "
                                "lean-facts gave it no Lean link; it counts as stale, not as credited")
    return errors, warnings


def valid_address(value: str) -> bool:
    """A page's or folder's node id: a relative path below roadmap/, without `.md`, `.` or `..` parts."""
    parts = value.split("/")
    return (not value.endswith(".md") and all(part and part not in (".", "..") for part in parts)
            and not value.startswith("/"))


def read_renames(path: Path) -> list[tuple[str, str]]:
    """The renamed roadmap files `git diff --name-status -M` lists, `R<score>\t<old>\t<new>` per line, as paths
    below roadmap/; other lines and files are ignored."""
    found = []
    prefix = "blueprint/roadmap/"
    for line in path.read_text().splitlines():
        fields = line.split("\t")
        if len(fields) == 3 and fields[0].startswith("R") and fields[1].startswith(prefix) and fields[2].startswith(prefix):
            found.append((fields[1][len(prefix):], fields[2][len(prefix):]))
    return found


def read_links(folder: Path) -> dict[Path, dict]:
    """The annotations of a links folder (the base commit's, say), by the page path they name below roadmap/, read as
    the checkout's are (by_page)."""
    return by_page({path.name: parse_rows(path.read_text()) for path in sorted(folder.glob("*.jsonl"))})


def check_moves(annotations: dict[Path, dict], cards: dict[Path, Card], base: str | None = None,
                required: bool = False, base_annotations: dict[Path, dict] | None = None,
                renames: list[tuple[str, str]] | None = None, text: str | None = None) -> list[str]:
    """The errors of scripts/card-moves.jsonl. The ledger only grows: given ``base``, the ledger the base commit
    published, its rows must stay, unchanged and first. Each chain is followed to its final live destination: a
    moved page or folder is no longer at its old path; every hop keeps the article id it started with, so an old
    address always leads to its own article; a page ends at a live statement page and a folder at a live folder
    page with that id, or at a card a retirement row then replaces; a retired card is no card any more, its id no
    page's, and what replaces it is one; a page ends at the address a statement's retirement row records for it, its
    id no page's or folder's any more, and its replacements end at a live statement page or folder page, through
    any retirement on the way; nothing goes round. An address has one owner: it moves once, as a page or as a folder,
    or is the last address of retired cards or of retired statements, each replaced in place by the next, and no
    live page or folder of another article takes it (a page or folder page with no id is another article's), but for
    the final replacement. ``required`` (the strict check): the file
    must exist. ``base_annotations``, the base commit's rows, and ``renames``, the roadmap files Git finds renamed
    since (old and new path below roadmap/): see `history`. ``text``: the ledger as its caller read it (the moves
    command reads it once, to check and hash the same bytes), instead of the file."""
    path = moves_file()
    published = [line for line in (base or "").splitlines() if line.strip()]
    if text is None:
        if not path.is_file():
            if required or published:
                return [f"{MOVES}: missing; it records every address a card change retired"]
            return []
        text = path.read_text()
    errors = []
    if base is not None:
        published = [line for line in base.splitlines() if line.strip()]
        if [line for line in text.splitlines() if line.strip()][:len(published)] != published:
            errors.append(f"{MOVES}: a row the base commit published was removed or changed; the ledger only grows")
    chains: dict[str, dict[str, tuple[str, str]]] = {"page": {}, "folder": {}}
    retired: dict[str, tuple[str, str]] = {}
    # A retired statement page, by id: what replaces it, and its last address.
    statements: dict[str, tuple[str, str]] = {}
    # The retirements at each address, of cards and of statements apart, in the ledger's order: line, id, replacement.
    claims: dict[str, dict[str, list[tuple[int, str, str]]]] = {"card": defaultdict(list),
                                                                 "statement": defaultdict(list)}
    card_ids = {card.id for card in cards.values() if isinstance(card.id, str)}
    by_id = {annotation["id"]: page for page, annotation in annotations.items() if isinstance(annotation.get("id"), str)}
    fresh: list[tuple[int, dict]] = []
    seen_rows = 0
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        seen_rows += 1
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            errors.append(f"{MOVES}:{number}: not JSON")
            continue
        if not isinstance(row, dict) or not all(isinstance(value, str) and value for value in row.values()):
            errors.append(f"{MOVES}:{number}: a row is an object of non-empty strings")
            continue
        if seen_rows > len(published):
            fresh.append((number, row))
        for kind in ("page", "folder"):
            if set(row) == {kind, "to", "article_id"}:
                if not ARTICLE_ID.fullmatch(row["article_id"]):
                    errors.append(f"{MOVES}:{number}: `article_id` is not an article id")
                if not (valid_address(row[kind]) and valid_address(row["to"])):
                    errors.append(f"{MOVES}:{number}: an address is a path below roadmap/ without `.md`")
                if row[kind] in chains[kind]:
                    errors.append(f"{MOVES}:{number}: {row[kind]} already moved")
                chains[kind][row[kind]] = (row["to"], row["article_id"])
                break
        else:
            if set(row) == {"card", "folder", "replaced_by"}:
                if not (ARTICLE_ID.fullmatch(row["card"]) and ARTICLE_ID.fullmatch(row["replaced_by"])):
                    errors.append(f"{MOVES}:{number}: `card` and `replaced_by` are article ids")
                if not valid_address(row["folder"]):
                    errors.append(f"{MOVES}:{number}: an address is a path below roadmap/ without `.md`")
                if row["card"] in retired:
                    errors.append(f"{MOVES}:{number}: the card {row['card']} is already retired")
                retired.setdefault(row["card"], (row["replaced_by"], row["folder"]))
                claims["card"][row["folder"]].append((number, row["card"], row["replaced_by"]))
            elif set(row) == {"statement", "page", "replaced_by"}:
                if not (ARTICLE_ID.fullmatch(row["statement"]) and ARTICLE_ID.fullmatch(row["replaced_by"])):
                    errors.append(f"{MOVES}:{number}: `statement` and `replaced_by` are article ids")
                if not valid_address(row["page"]):
                    errors.append(f"{MOVES}:{number}: an address is a path below roadmap/ without `.md`")
                if row["statement"] in statements:
                    errors.append(f"{MOVES}:{number}: the statement {row['statement']} is already retired")
                statements.setdefault(row["statement"], (row["replaced_by"], row["page"]))
                claims["statement"][row["page"]].append((number, row["statement"], row["replaced_by"]))
            else:
                errors.append(f"{MOVES}:{number}: expected {{page, to, article_id}}, {{folder, to, article_id}}, "
                              "{card, folder, replaced_by} or {statement, page, replaced_by}")

    # An address has one owner: the retirements at one address are one history, each replaced in place by the next,
    # in the ledger's order; two that are not would be two articles claiming it, and no order may choose between them.
    for kind, at_address in claims.items():
        for address, found in sorted(at_address.items()):
            for (_, one, successor), (number, two, _) in zip(found, found[1:]):
                if successor != two:
                    errors.append(f"{MOVES}:{number}: {address} is the last address of the retired {kind} {one}, "
                                  f"replaced by {successor}, and of {two}; an address has one owner, so each "
                                  "retirement there is replaced in place by the next")

    def replacement(card_id: str) -> str | None:
        """The live card a retired card's replacements end at, or None (an error said why)."""
        seen, at = {card_id}, retired[card_id][0]
        while at in retired:
            if at in seen:
                errors.append(f"{MOVES}: the replacements of {card_id} go round")
                return None
            seen.add(at)
            at = retired[at][0]
        if at not in card_ids:
            errors.append(f"{MOVES}: the retired card {card_id} is replaced by {at}, which is no card")
            return None
        return at

    def successor(statement: str) -> str | None:
        """The live statement page or folder page a retired statement's replacements end at, through every statement
        or card retired on the way, or None (an error said why)."""
        seen, at = {statement}, statements[statement][0]
        while at in statements or at in retired:
            if at in seen:
                errors.append(f"{MOVES}: the replacements of {statement} go round")
                return None
            seen.add(at)
            at = (statements if at in statements else retired)[at][0]
        page = by_id.get(at)
        if page is None or not page.is_file():
            errors.append(f"{MOVES}: the retired statement {statement} is replaced by {at}, which is no live page or "
                          "folder")
            return None
        return at

    for old in sorted(set(chains["page"]) & set(chains["folder"])):
        errors.append(f"{MOVES}: {old} moved both as a page and as a folder; an address has one owner")
    ids_at = {node_id(page): annotation.get("id") for page, annotation in annotations.items() if page.is_file()}
    for kind, chain in chains.items():
        for old in sorted(chain):
            here = (wiki.ROADMAP / (f"{old}/README.md" if kind == "folder" else f"{old}.md"))
            other = (wiki.ROADMAP / (f"{old}.md" if kind == "folder" else f"{old}/README.md"))
            if here.is_file():
                errors.append(f"{MOVES}: the {kind} {old} moved but is still there")
            elif other.is_file() and ids_at.get(old) != chain[old][1]:
                errors.append(f"{MOVES}: {old} moved as a {kind}, and another article's "
                              f"{'page' if kind == 'folder' else 'folder'} now holds the address")
            seen, at, article_id = {old}, *chain[old]
            while at in chain:
                if at in seen:
                    errors.append(f"{MOVES}: the moves of {old} go round")
                    break
                seen.add(at)
                if chain[at][1] != article_id:
                    errors.append(f"{MOVES}: {old} moved as {article_id} to {at}, which moved on as {chain[at][1]}; "
                                  "an old address must keep leading to its own article")
                at, article_id = chain[at]
            else:
                page = by_id.get(article_id)
                live = None if page is None or not page.is_file() else node_id(page)
                if kind == "page":
                    if article_id in statements and page is None:
                        if statements[article_id][1] != at:
                            errors.append(f"{MOVES}: the page {old} ends at {at}, but its statement {article_id} was "
                                          f"retired at {statements[article_id][1]}")
                    elif live is None or page.name == "README.md" or live != at:
                        errors.append(f"{MOVES}: {old} ends at {at}, but {article_id} is "
                                      f"{live or 'no statement page'}")
                if kind == "folder":
                    if article_id in retired and page is None:
                        if retired[article_id][1] != at:
                            errors.append(f"{MOVES}: the folder {old} ends at {at}, but its card {article_id} was "
                                          f"retired at {retired[article_id][1]}")
                    elif live is None or page.name != "README.md" or live != at:
                        errors.append(f"{MOVES}: the folder {old} ends at {at}, but {article_id} is "
                                      f"{live or 'no folder page'}")
    finals: dict[str, str | None] = {}
    for old in sorted(retired):
        page = by_id.get(old)
        # A folder may stay a plain folder with its id once its card is retired (declassified); no card and no
        # statement page carries a retired id.
        if page is not None and (page.name != "README.md" or page.parent in cards):
            errors.append(f"{MOVES}: the retired card {old} is still the id of {node_id(page)}")
        finals[old] = replacement(old)
    for card_id, (_, folder) in sorted(retired.items()):
        if folder in chains["page"] or folder in chains["folder"]:
            errors.append(f"{MOVES}: {folder} is the last address of the retired card {card_id} and moved too; an "
                          "address has one owner")
        # An address a page or folder page holds is taken, with an id or without: only the card itself, a folder
        # keeping its id once declassified, or its final replacement may hold it.
        occupant = ids_at.get(folder)
        if occupant is None and ((wiki.ROADMAP / folder / "README.md").is_file()
                                 or (wiki.ROADMAP / f"{folder}.md").is_file()):
            errors.append(f"{MOVES}: the retired card {card_id}'s address {folder} is held by an article with no id")
        elif occupant is not None and occupant not in (card_id, finals[card_id]):
            errors.append(f"{MOVES}: the retired card {card_id}'s address {folder} is held by another article")
    successors: dict[str, str | None] = {}
    folders = {folder for _, folder in retired.values()}
    for statement, (_, address) in sorted(statements.items()):
        page = by_id.get(statement)
        if page is not None:
            errors.append(f"{MOVES}: the retired statement {statement} is still the id of {node_id(page)}")
        if statement in retired:
            errors.append(f"{MOVES}: {statement} is retired both as a card and as a statement")
        successors[statement] = successor(statement)
        if address in chains["page"] or address in chains["folder"] or address in folders:
            errors.append(f"{MOVES}: {address} is the last address of the retired statement {statement} and moved or "
                          "was a retired card's too; an address has one owner")
        # As for a card: the address is taken by any page or folder page, with an id or without, but the final
        # replacement, which may live there.
        occupant = ids_at.get(address)
        if occupant is None and ((wiki.ROADMAP / f"{address}.md").is_file()
                                 or (wiki.ROADMAP / address / "README.md").is_file()):
            errors.append(f"{MOVES}: the retired statement {statement}'s address {address} is held by an article with "
                          "no id")
        elif occupant is not None and occupant != successors[statement]:
            errors.append(f"{MOVES}: the retired statement {statement}'s address {address} is held by another article")
    if base_annotations is not None:
        published_rows = [json.loads(line) for line in published]
        errors += reconcile(base_annotations, annotations, cards, fresh, published_rows, retired, finals,
                            renames or [], statements, successors)
    return errors


@dataclass
class Article:
    """A statement page or folder page as one snapshot has it: its kind, address, `id`, declaration and whether
    its folder is a card."""

    kind: str
    address: str
    id: str | None
    name: str | None
    card: bool


def articles(annotations: dict[Path, dict], live: bool) -> list[Article]:
    found = []
    for page, annotation in sorted(annotations.items()):
        if live and not page.is_file():
            continue
        kind = "folder" if page.name == "README.md" else "page"
        own = annotation.get("extensions", {}).get(OWN)
        found.append(Article(kind, node_id(page), annotation.get("id") if isinstance(annotation.get("id"), str) else None,
                             declaration(annotation) if kind == "page" else None,
                             kind == "folder" and isinstance(own, dict) and "card" in own))
    return found


def reconcile(base_annotations: dict[Path, dict], annotations: dict[Path, dict], cards: dict[Path, Card],
              fresh: list[tuple[int, dict]], published_rows: list[dict], retired: dict[str, tuple[str, str]],
              finals: dict[str, str | None], renames: list[tuple[str, str]],
              statements: dict[str, tuple[str, str]] | None = None,
              successors: dict[str, str | None] | None = None) -> list[str]:
    """Every change of address or identity since the base commit, against the rows added since, with one map of
    who owns what. An article of the base is found in the checkout by its `id`; one without an `id` by its
    address (an `id` minted in place), else by its declaration when exactly one page credits it on each side,
    else by Git's rename of its file (``renames``), which never overrides a known `id` or declaration. Two
    articles never become one, and one never becomes two. The rows added since are replayed in order over the
    base's addresses: each moves what its old address holds at that point, with that article's `id` (or, for an
    article that had none, an `id` no other article of the base or the ledger ever had), and a folder row moves the
    folder alone, so each page and folder inside it that moves needs its own row; a retirement names the card's or
    the statement's address at that point (``statements``, by id: what replaces each and its last address;
    ``successors``, the live article each one's replacements end at). Afterwards every article stands where the rows
    leave it and keeps its `id`, or is a statement page the rows retire; an address that changed hands is a retired
    card's or statement's, held by its final replacement; and every card of the base that is no card any more has
    its retirement."""
    statements, successors = statements or {}, successors or {}
    errors: list[str] = []
    base, head = articles(base_annotations, live=False), articles(annotations, live=True)
    head_by_id = {article.id: article for article in head if article.id}
    head_at = {(article.kind, article.address): article for article in head}
    # One article per address, whatever its kind: a page `b.md` beside a folder `b/` would be one node.
    for article in head:
        if article.kind == "page" and (wiki.ROADMAP / article.address / "README.md").is_file():
            errors.append(f"{MOVES}: {article.address} is both a page and a folder; an address has one article")

    def unique(found: list[Article]) -> dict[str, Article]:
        counts = Counter(article.name for article in found if article.name)
        return {article.name: article for article in found if article.name and counts[article.name] == 1}

    base_names, head_names = unique(base), unique(head)
    match: dict[int, Article] = {}
    claimed: dict[int, Article] = {}

    def claim(old: Article, new: Article, how: str) -> None:
        if id(new) in claimed and claimed[id(new)] is not old:
            errors.append(f"{MOVES}: {claimed[id(new)].address} and {old.address} both became {new.address} "
                          f"({how}); two articles stay two")
        elif id(old) in match and match[id(old)] is not new:
            errors.append(f"{MOVES}: {old.address} became both {match[id(old)].address} and {new.address} ({how})")
        else:
            match[id(old)], claimed[id(new)] = new, old

    for old in base:
        if old.id and old.id in head_by_id:
            new = head_by_id[old.id]
            if new.kind != old.kind:
                errors.append(f"{MOVES}: {old.id} was the {old.kind} {old.address} and is now the {new.kind} "
                              f"{new.address}")
            else:
                claim(old, new, "its id")
    for old in base:
        new = head_at.get((old.kind, old.address))
        if old.id is None and id(old) not in match and new is not None and id(new) not in claimed:
            claim(old, new, "its address")
    for old in base:
        if old.name in base_names and old.name in head_names:
            new = head_names[old.name]
            if old.id and new.id and old.id != new.id:
                errors.append(f"{MOVES}: {old.address} credited {old.name} as {old.id}; {new.address} credits it as "
                              f"{new.id}; an article keeps its id")
            elif match.get(id(old)) is not new:
                claim(old, new, f"its declaration {old.name}")
    renamed = dict(renames)
    for old in base:
        # Git's rename speaks only for an article nothing else found: never against a known id or declaration, nor for
        # a statement a row retires, whose prose its successors may have taken.
        if id(old) in match or (old.id and old.id in head_by_id) or (old.name in base_names
                                                                     and old.name in head_names):
            continue
        if old.kind == "page" and old.id in statements:
            continue
        target = renamed.get(f"{old.address}.md" if old.kind == "page" else f"{old.address}/README.md")
        if target is not None:
            path = wiki.ROADMAP / target
            new = head_at.get(("folder" if path.name == "README.md" else "page", node_id(path)))
            if new is not None and id(new) not in claimed:
                claim(old, new, "Git's rename")

    # Replay the rows added since over the base's addresses.
    where = {id(old): (old.kind, old.address) for old in base}
    owner = {(old.kind, old.address): old for old in base}
    assigned: dict[int, str] = {}
    used = {old.id for old in base if old.id} | set(retired) | set(statements) | {
        row["article_id"] for row in published_rows if isinstance(row, dict) and "article_id" in row}
    retiring: set[int] = set()
    by_base_id = {old.id: old for old in base if old.id}
    for number, row in fresh:
        if set(row) in ({"page", "to", "article_id"}, {"folder", "to", "article_id"}):
            kind = "page" if "page" in row else "folder"
            old_address, new_address, article_id = row[kind], row["to"], row["article_id"]
            moving = owner.get((kind, old_address))
            if moving is None:
                errors.append(f"{MOVES}:{number}: no {kind} is at {old_address} when this row moves it")
                continue
            current = moving.id or assigned.get(id(moving))
            if current is None:
                if article_id in used:
                    errors.append(f"{MOVES}:{number}: {old_address} had no id, and {article_id} is another "
                                  "article's")
                    continue
                assigned[id(moving)] = article_id
                used.add(article_id)
            elif current != article_id:
                errors.append(f"{MOVES}:{number}: {old_address} is {current}, not {article_id}")
                continue
            # A folder row moves the folder alone, its folder page and its address: each page and folder inside it
            # that moves has its own row, so the history never depends on what the folder holds later.
            del owner[(kind, old_address)]
            if ("page", new_address) in owner or ("folder", new_address) in owner:
                errors.append(f"{MOVES}:{number}: {new_address} already holds another article")
            owner[(kind, new_address)] = moving
            where[id(moving)] = (kind, new_address)
        elif set(row) == {"card", "folder", "replaced_by"}:
            card = by_base_id.get(row["card"])
            if card is None or not card.card:
                errors.append(f"{MOVES}:{number}: {row['card']} was no card at the base commit")
                continue
            if where[id(card)] != ("folder", row["folder"]):
                errors.append(f"{MOVES}:{number}: the card {row['card']} is at {where[id(card)][1]}, not "
                              f"{row['folder']}")
            retiring.add(id(card))
            # Retired, the card leaves its address free: its replacement may move in by a later row, never before.
            if owner.get(("folder", row["folder"])) is card:
                del owner[("folder", row["folder"])]
        elif set(row) == {"statement", "page", "replaced_by"}:
            statement = by_base_id.get(row["statement"])
            if statement is None or statement.kind != "page":
                errors.append(f"{MOVES}:{number}: {row['statement']} was no statement page at the base commit")
                continue
            if where[id(statement)] != ("page", row["page"]):
                errors.append(f"{MOVES}:{number}: the statement {row['statement']} is at {where[id(statement)][1]}, "
                              f"not {row['page']}")
            retiring.add(id(statement))
            # As for a card: its address is free once it is retired, for its replacement to move in by a later row.
            if owner.get(("page", row["page"])) is statement:
                del owner[("page", row["page"])]

    # Every article of the base stands where the rows leave it, or is gone with its retirement.
    for old in base:
        new = match.get(id(old))
        moved_to = where[id(old)]
        expected = old.id or assigned.get(id(old))
        gone = (old.card and old.id in retired) or (old.kind == "page" and old.id in statements)
        if new is not None:
            if moved_to != (new.kind, new.address):
                if moved_to == (old.kind, old.address):
                    errors.append(f"{MOVES}: {old.address} is now {new.address}, and no row leads there")
                else:
                    errors.append(f"{MOVES}: {old.address} is now {new.address}, but its rows lead to {moved_to[1]}")
            if expected is not None and new.id != expected:
                errors.append(f"{MOVES}: {new.address} was {expected} and is now {new.id}; an article keeps its id")
            elif expected is None and new.id is not None and new.id in used:
                errors.append(f"{MOVES}: {new.address} took {new.id}, which another article had")
        elif moved_to == (old.kind, old.address) and not gone:
            # Gone, and no row moves it: its old address would lead nowhere, and could be taken by another.
            errors.append(f"{MOVES}: {old.address} ({old.id or 'no id'}) is gone, and no row moves it; an article "
                          "keeps its address or moves with its row")
        elif moved_to != (old.kind, old.address) and not gone:
            landed = head_at.get(moved_to)
            if landed is None:
                errors.append(f"{MOVES}: the rows move {old.address} to {moved_to[1]}, where nothing is")
            elif id(landed) in claimed:
                errors.append(f"{MOVES}: the rows move {old.address} to {moved_to[1]}, which is "
                              f"{claimed[id(landed)].address}'s; two articles stay two")
            else:
                claimed[id(landed)] = old
                if expected is not None and landed.id != expected:
                    errors.append(f"{MOVES}: {landed.address} should be {expected}, and is {landed.id}")
    # An address held by another article than at the base: only a retired card's or statement's final replacement.
    for old in base:
        here = head_at.get((old.kind, old.address))
        if old.id and here is not None and here.id != old.id and claimed.get(id(here)) is not old:
            if not (here.id is not None and (finals.get(old.id) if old.id in retired
                                             else successors.get(old.id)) == here.id):
                errors.append(f"{MOVES}: {old.address} was {old.id} and now holds {here.id}; only a retired card's "
                              "or statement's final replacement takes its address")
    # Every card of the base that is no card any more is retired.
    live_cards = {card.id for card in cards.values()}
    for old in base:
        if old.card and old.id not in live_cards and old.id not in retired:
            errors.append(f"{MOVES}: the card {old.id} at {old.address} is no card any more, and no row retires it")
    # An article new since the base takes an id no article ever had.
    for new in head:
        if new.id and id(new) not in claimed and new.id in used:
            errors.append(f"{MOVES}: {new.address} takes {new.id}, which another article had")
    return errors


def resolved_names(graph, annotations: dict[Path, dict], dependencies: dict) -> dict[str, str]:
    """The declaration each ATLAS-credited statement page that Autoform loaded stands for, by page id: the one its
    build row's Lean link names. A row an earlier sync wrote with a module and a name has one once lean-facts
    resolved it through the Lean index (sync_wiki.legacy_lean_name, the one decision); one it did not resolve stands
    for nothing, however few of the extraction's articles share its module and name, and is no current credit (the
    graph rules' Writing pages)."""
    names = {}
    for path, page in statement_nodes(graph).items():
        annotation = annotations.get(page)
        if credit(annotation) == "atlas" and (name := declaration(annotation)) is not None:
            names[path] = name
    return names


def mathlib_credit_problems(graph, annotations: dict[Path, dict], committed: dict[Path, dict] | None,
                            registry: dict | None, owners: set[str] | None = None) -> list[str]:
    """What the edges cannot show about Mathlib credit. The committed rows credit no declaration ambiguously and none
    twice; with the registry, it was made from their list of credited names (sync_wiki.registry_problems), and the
    declarations it found are exactly those the build's statement pages credit to Mathlib, one page each, each page
    with the registry's kind: a page whose declaration the registry did not find was unlinked by lean-facts, and a
    page the registry has no row for is an error, never shown as in Mathlib."""
    files = {sync.LINKS: list((committed or {}).values())}
    _, problems = sync.credited_mathlib(files)
    errors = list(problems)
    if registry is None or errors:
        return errors
    errors += sync.registry_problems(registry, files, owners)
    if errors:
        return errors
    built: dict[str, list[str]] = defaultdict(list)
    pages = statement_nodes(graph)
    committed_names = {page: declaration(row) for page, row in (committed or {}).items() if credit(row) == "mathlib"}
    for node, page in sorted(pages.items()):
        annotation = annotations.get(page)
        if credit(annotation) == "mathlib":
            built[declaration(annotation) or ""].append(node)
            # Each page keeps the declaration its committed row credits.
            if committed_names.get(page) != declaration(annotation):
                errors.append(f"{node}: the build credits {declaration(annotation)}, but its committed row credits "
                              f"{committed_names.get(page)}")
    found = registry["mathlib"]
    for name, nodes in sorted(built.items()):
        if name not in found:
            errors.append(f"{nodes[0]}: credits the Mathlib declaration {name or '?'}, which the registry does not "
                          "find")
        elif len(nodes) > 1:
            errors.append(f"{', '.join(nodes)}: all credit the Mathlib declaration {name}; a declaration has one page")
        elif (kind := annotations[pages[nodes[0]]].get("kind")) != found[name].get("kind"):
            errors.append(f"{nodes[0]}: its kind is {kind!r}, but the registry finds {name} a "
                          f"`{found[name].get('kind')}`; run sync_wiki.py lean-facts with this registry")
    for name in sorted(found.keys() - built.keys()):
        errors.append(f"the registry finds the Mathlib declaration {name}, which no statement page of the build "
                      "credits")
    return errors


def integrity(graph, annotations: dict[Path, dict], dependencies: dict, registry: dict | None = None) -> list[str]:
    """The differences between the dependencies of the checkout and the extraction lean-facts wrote them from, as
    sets of oriented typed edges, both ways: every dependency of an ATLAS-credited statement page must be a typed
    edge the extraction records, and every edge it records between two declarations that credit statement pages
    must be a dependency of the checkout, of the same kind. lean-facts writes a dependency that is both a statement
    and a proof dependency as a statement one, so a page never lists one target under both. An edge that leaves a
    Mathlib-credited page, or reaches one from an ATLAS-credited page, cannot be checked against this extraction,
    which records only the project's declarations: it is an error, never shown as compiled, unless ``registry`` (the
    build's Mathlib registry, `extract_v2_lean_dependencies.py --registry`) is given: then the edges from
    ATLAS-credited to Mathlib-credited pages must equal its bridges, and those between Mathlib-credited pages its
    Mathlib edges, as typed sets both ways."""
    articles = dependencies.get("articles", {})
    pages = {path: annotations.get(page) for path, page in statement_nodes(graph).items()}
    name_of = resolved_names(graph, annotations, dependencies)
    page_of = {name: path for path, name in name_of.items()}
    errors = []
    # A page that credits a declaration of this project by its Lean link, and whose kind lean-facts found, has its
    # row in the extraction, even one with no edges: otherwise the extraction was made for another state of the
    # wiki, and the page would show no prerequisites.
    for path, annotation in sorted(pages.items()):
        name = declaration(annotation) if credit(annotation) == "atlas" else None
        if name is not None and "kind" in (annotation or {}) and name not in articles:
            errors.append(f"{path}: credits {name}, which the extraction has no row for; it was made for another "
                          "state of the wiki")
    rendered: dict[tuple[str, str], set[str]] = defaultdict(set)
    linked: dict[tuple[str, str], set[str]] = defaultdict(set)
    for node in sorted(graph.nodes.values(), key=lambda node: node.id):
        source_credit = credit(pages.get(node.id))
        for kind, targets in (("statement", node.statement_dependencies), ("proof", node.proof_dependencies)):
            for target in targets:
                target_credit = credit(pages.get(target))
                if source_credit == "mathlib":
                    if registry is None or target_credit != "mathlib":
                        errors.append(f"{node.id}: a Mathlib-credited page lists a {kind} dependency on {target}; "
                                      "nothing here can check it")
                    else:
                        linked[(node.id, target)].add(kind)
                    continue
                if source_credit != "atlas":
                    continue
                if target_credit == "mathlib":
                    if registry is None:
                        errors.append(f"{node.id}: its {kind} dependency on the Mathlib-credited page {target} "
                                      "cannot be checked against the extraction")
                    else:
                        linked[(node.id, target)].add(kind)
                    continue
                if target_credit != "atlas" or node.id not in name_of or target not in name_of:
                    errors.append(f"{node.id}: its {kind} dependency {target} joins no two declarations the "
                                  "extraction can record")
                    continue
                rendered[(node.id, target)].add(kind)
    for (source, target), kinds in sorted(rendered.items()):
        if len(kinds) > 1:
            errors.append(f"{source}: lists {target} as both a statement and a proof dependency")
    shown = {(source, target, "statement" if "statement" in kinds else "proof")
             for (source, target), kinds in rendered.items()}
    extracted_kinds: dict[tuple[str, str], set[str]] = defaultdict(set)
    for name, entry in sorted(articles.items()):
        if name not in page_of:
            errors.append(f"the extraction records {name}, which credits no statement page")
            continue
        for kind in ("statement", "proof"):
            for other in entry.get(kind, []):
                if other == name:
                    continue
                if other not in page_of:
                    errors.append(f"the extraction records {name} -> {other}, and {other} credits no statement page")
                    continue
                extracted_kinds[(page_of[name], page_of[other])].add(kind)
    recorded = {(source, target, "statement" if "statement" in kinds else "proof")
                for (source, target), kinds in extracted_kinds.items()}
    for source, target, kind in sorted(shown - recorded):
        other = "proof" if kind == "statement" else "statement"
        if (source, target, other) in recorded:
            errors.append(f"{source}: its dependency {target} is a {kind} dependency, but the extraction records a "
                          f"{other} one")
        else:
            errors.append(f"{source}: its {kind} dependency {target} is not in the extraction")
    for source, target, kind in sorted(recorded - shown):
        other = "proof" if kind == "statement" else "statement"
        if (source, target, other) not in shown:
            errors.append(f"{source}: the extraction records a {kind} dependency on {target}, which the page lacks")
    if registry is not None:
        errors += registry_differences(pages, name_of, linked, registry)
    return errors


def registry_differences(pages: dict[str, dict | None], name_of: dict[str, str],
                         linked: dict[tuple[str, str], set[str]], registry: dict) -> list[str]:
    """The differences, as typed sets both ways, between the edges that reach Mathlib-credited pages and the
    registry the build wrote them from: its bridges (ATLAS declaration to Mathlib declaration) and its Mathlib
    edges (between Mathlib declarations), each between two declarations that credit statement pages."""
    errors = []
    mathlib_page = {declaration(annotation): path for path, annotation in pages.items() if credit(annotation) == "mathlib"}
    atlas_page = {name: path for path, name in name_of.items()}
    for (source, target), kinds in sorted(linked.items()):
        if len(kinds) > 1:
            errors.append(f"{source}: lists the Mathlib-credited {target} as both a statement and a proof dependency")
    shown = {(source, target, "statement" if "statement" in kinds else "proof")
             for (source, target), kinds in linked.items()}
    expected_kinds: dict[tuple[str, str], set[str]] = defaultdict(set)
    for table, sources in (("bridges", atlas_page), ("mathlib", mathlib_page)):
        for name, entry in sorted(registry.get(table, {}).items()):
            # An edge the registry records between declarations that do not each credit one statement page is an
            # error, never left out of the comparison.
            if name not in sources:
                errors.append(f"the registry records the dependencies of {name}, which credits no statement page")
                continue
            for kind in ("statement", "proof"):
                for other in entry.get(kind, []):
                    if other not in mathlib_page:
                        errors.append(f"the registry records {name} -> {other}, and {other} credits no statement page")
                    elif mathlib_page[other] != sources[name]:
                        expected_kinds[(sources[name], mathlib_page[other])].add(kind)
    expected = {(source, target, "statement" if "statement" in kinds else "proof")
                for (source, target), kinds in expected_kinds.items()}
    for source, target, kind in sorted(shown - expected):
        other = "proof" if kind == "statement" else "statement"
        if (source, target, other) in expected:
            errors.append(f"{source}: its dependency on the Mathlib-credited {target} is a {kind} dependency, but the "
                          f"registry records a {other} one")
        else:
            errors.append(f"{source}: its {kind} dependency on the Mathlib-credited {target} is not in the registry")
    for source, target, kind in sorted(expected - shown):
        other = "proof" if kind == "statement" else "statement"
        if (source, target, other) not in shown:
            errors.append(f"{source}: the registry records a {kind} dependency on the Mathlib-credited {target}, "
                          "which the page lacks")
    return errors


def example_cycle(edges: dict, component: list) -> list:
    """A closed walk inside a strongly connected component of two or more vertices, in a fixed order: from its
    smallest vertex, always to the smallest successor inside it, until a vertex repeats; the walk from that vertex."""
    members, at = set(component), component[0]
    path, seen = [at], {at}
    while True:
        at = min(target for target in edges.get(at, []) if target in members)
        if at in seen:
            return path[path.index(at):] + [at]
        path.append(at)
        seen.add(at)


def cycles(edges: dict) -> list[list]:
    """One closed walk in each strongly connected component of two or more vertices (see example_cycle)."""
    return [example_cycle(edges, component) for component in strongly_connected(edges) if len(component) > 1]


def strongly_connected(edges: dict) -> list[list]:
    """Tarjan's components, each sorted, in sorted order; iterative, so deep graphs do not overflow the stack."""
    vertices = sorted(set(edges) | {target for targets in edges.values() for target in targets})
    index: dict = {}
    low: dict = {}
    stack: list = []
    on_stack: set = set()
    components = []
    counter = 0
    for root in vertices:
        if root in index:
            continue
        work = [(root, iter(sorted(edges.get(root, []))))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            vertex, successors = work[-1]
            advanced = False
            for target in successors:
                if target not in index:
                    index[target] = low[target] = counter
                    counter += 1
                    stack.append(target)
                    on_stack.add(target)
                    work.append((target, iter(sorted(edges.get(target, [])))))
                    advanced = True
                    break
                if target in on_stack:
                    low[vertex] = min(low[vertex], index[target])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[vertex])
            if low[vertex] == index[vertex]:
                component = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component.append(member)
                    if member == vertex:
                        break
                components.append(sorted(component))
    return sorted(components)


def load_graph():
    from autoform_cli.graph import load_graph as autoform_graph

    return autoform_graph(wiki.VAULT)


def shortest_walks(source: str, edges: dict[str, list[str]], stop: set[str]) -> dict[str, list[str]]:
    """The shortest walk from ``source`` to each vertex of ``stop`` that it reaches without passing through another
    vertex of ``stop``, ties broken by the smallest sequence of vertex ids. Breadth first, a level at a time: a vertex
    takes as its predecessor the one, on the level before, whose own walk is smallest."""
    walks = {source: [source]}
    level = [source]
    found: dict[str, list[str]] = {}
    while level:
        rank = {vertex: position for position, vertex in enumerate(level)}
        best: dict[str, str] = {}
        for vertex in level:
            if vertex in stop and vertex != source:
                continue
            for target in edges.get(vertex, []):
                if target in walks:
                    continue
                if target not in best or rank[vertex] < rank[best[target]]:
                    best[target] = vertex
        following = sorted(best, key=lambda target: (rank[best[target]], target))
        for target in following:
            walks[target] = walks[best[target]] + [target]
            if target in stop:
                found[target] = walks[target]
        level = following
    return found


@dataclass
class Leaf:
    """What the derived data says about one statement page."""

    credit: str
    article_id: str | None
    held: bool
    not_ready: bool
    stale: bool
    state: str | None
    kind: str | None


def rollup(dependencies: dict, annotations: dict[Path, dict] | None = None, graph=None,
           committed: dict[Path, dict] | None = None, commit: str | None = None, checked: bool = False,
           registry: dict | None = None) -> dict:
    """The cards with their status and progress, and their derived edges with the dependencies that witness them,
    from the edges the strict check validated against ``dependencies`` (the extraction): every edge between two
    ATLAS-credited pages is then one it records, so `compiled` is a checked origin. Unless the caller already ran
    that check on the same inputs (``checked``), it runs here, and an error stops the rollup."""
    from autoform_cli.status import derive

    annotations = read_annotations() if annotations is None else annotations
    committed = annotations if committed is None else committed
    cards = card_folders(annotations)
    graph = load_graph() if graph is None else graph
    if not checked:
        errors, _ = check(annotations, graph, committed, dependencies, registry=registry)
        if errors:
            raise ValueError("the strict check fails: " + "; ".join(errors[:5]))
    statuses = derive(graph)
    pages = statement_nodes(graph)
    by_id = {annotation["id"]: page for page, annotation in annotations.items() if isinstance(annotation.get("id"), str)}
    resolved = resolved_names(graph, annotations, dependencies)

    def current_credit(path: str, annotation: dict | None) -> str:
        """A module-and-name row counts as ATLAS credit only once lean-facts gave it its declaration's Lean link."""
        found = credit(annotation)
        if found == "atlas" and declaration(annotation) is None and path not in resolved:
            return "none"
        return found

    def leaf(path: str) -> Leaf:
        page = pages.get(path)
        built, authored = annotations.get(page, {}), committed.get(page, {})
        own = authored.get("extensions", {}).get(OWN, {})
        status = statuses.get(path)
        built_credit = current_credit(path, built)
        return Leaf(credit=built_credit, article_id=authored.get("id") or built.get("id"),
                    held="held" in own if isinstance(own, dict) else False,
                    not_ready=authored.get("extensions", {}).get(AUTOFORM, {}).get("not_ready") is True,
                    stale=credit(authored) != "none" and built_credit == "none",
                    state=status.state.key if status is not None else None, kind=built.get("kind"))

    home: dict[str, str] = {}
    mains: dict[str, str] = {}
    for folder, card in cards.items():
        for member in leaves(folder):
            home[node_id(member)] = card.id
        mains[node_id(by_id[card.record["main_article_id"]])] = card.id
    mentioned: set[str] = set(home)

    def bucket(path: str) -> str:
        about = leaf(path)
        for marker, holds in (("stale", about.stale), ("held", about.held), ("not_ready", about.not_ready),
                              ("page_only", about.credit == "none" and about.kind is None)):
            if holds:
                return marker
        return about.state if about.state in STATES else "planned"

    out_cards = []
    for folder, card in cards.items():
        members = [node_id(page) for page in leaves(folder)]
        main = node_id(by_id[card.record["main_article_id"]])
        supporting = [member for member in members if member != main]
        counts = Counter(bucket(member) for member in supporting)
        about = leaf(main)
        supports = sorted(node_id(by_id[other]) for other in card.record.get("supports", []))
        mentioned.update(supports)
        out_cards.append({
            "id": card.id,
            "folder": card.node,
            # The title as the site renders it, the one the check validated.
            "title": page_view((folder / "README.md").read_text()).title,
            "kind": card.record["kind"],
            "importance": card.record["importance"],
            "level": card.record["level"],
            "main": {"page": main, "article_id": card.record["main_article_id"], "headline": bucket(main),
                     "state": about.state, "credit": about.credit, "held": about.held, "not_ready": about.not_ready,
                     "stale": about.stale},
            "pages": members,
            "supports": supports,
            "seeds": sorted(card.record.get("seeds", []), key=lambda seed: json.dumps(seed, sort_keys=True)),
            "supporting": {"total": len(supporting), **{key: counts.get(key, 0) for key in BUCKETS}},
        })

    def origin(source: str, target: str) -> str:
        """`planned` from a page-only page (its editors wrote it, as Writing pages says); `compiled` between two
        ATLAS-credited pages, which the check matched against the extraction; `bridge` (ATLAS to Mathlib) and
        `mathlib` (between Mathlib-credited pages), which it matched against the registry. No other pair passes."""
        source_credit, target_credit = leaf(source).credit, leaf(target).credit
        if source_credit == "none":
            return "planned"
        found = {("atlas", "atlas"): "compiled", ("atlas", "mathlib"): "bridge",
                 ("mathlib", "mathlib"): "mathlib"}.get((source_credit, target_credit))
        if found is None or (found != "compiled" and registry is None):
            raise AssertionError(f"{source} -> {target}: an edge the check does not allow")
        return found

    edges: dict[str, list[tuple[str, str]]] = defaultdict(list)
    witnesses: dict[tuple[str, str], set[tuple[str, str, str]]] = defaultdict(set)
    accounting = Counter()
    subjects = {card.node.split("/")[0] for card in cards.values()}
    for node in graph.nodes.values():
        statement = set(node.statement_dependencies)
        # The extraction writes a dependency that is both kinds as a statement one; a page-only page's editors may
        # name one under both, and both are kept.
        proof = set(node.proof_dependencies)
        if node.id in pages and leaf(node.id).credit != "none":
            proof -= statement
        for kind, targets in (("statement", sorted(statement)), ("proof", sorted(proof))):
            for target in targets:
                if node.id in pages and target in pages:
                    edges[node.id].append((target, kind))
                if node.id not in home:
                    continue
                accounting["total"] += 1
                if home.get(target) == home[node.id]:
                    accounting["internal"] += 1
                elif target in home:
                    accounting["card_to_card"] += 1
                    witnesses[(home[node.id], home[target])].add((node.id, target, kind))
                elif target not in pages:
                    accounting["to_folder"] += 1
                elif target.split("/")[0] in subjects:
                    accounting["to_unassigned"] += 1
                else:
                    accounting["to_subject_without_cards"] += 1
    for vertex in edges:
        edges[vertex] = sorted(set(edges[vertex]))
    if accounting["total"] != sum(accounting[key] for key in ("internal", "card_to_card", "to_unassigned",
                                                              "to_subject_without_cards", "to_folder")):
        raise AssertionError("the edge accounting does not add up")

    def step(source: str, target: str, kind: str) -> dict:
        mentioned.update((source, target))
        return {"source": source, "target": target, "kind": kind, "origin": origin(source, target)}

    uses = []
    for (source, target), found in sorted(witnesses.items()):
        typed = [step(*witness) for witness in sorted(found)]
        uses.append({"from": source, "to": target,
                     "statement": sum(w["kind"] == "statement" for w in typed),
                     "proof": sum(w["kind"] == "proof" for w in typed),
                     "origins": dict(sorted(Counter(w["origin"] for w in typed).items())),
                     "witnesses": typed})
    any_edges = {vertex: sorted({target for target, _ in targets}) for vertex, targets in edges.items()}
    statement_edges = {vertex: sorted({target for target, kind in targets if kind == "statement"})
                       for vertex, targets in edges.items()}

    def typed_walk(walk: list[str], statement_only: bool) -> list[dict]:
        steps = []
        for source, target in zip(walk, walk[1:]):
            kinds = {kind for other, kind in edges[source] if other == target}
            steps.append(step(source, target, "statement" if "statement" in kinds else "proof"))
            if statement_only and "statement" not in kinds:
                raise AssertionError("a statement walk took a proof step")
        return steps

    stop = set(mains)
    needs = []
    for card in out_cards:
        main = card["main"]["page"]
        reached = shortest_walks(main, any_edges, stop)
        by_statement = shortest_walks(main, statement_edges, stop)
        for target, walk in sorted(reached.items()):
            if target in by_statement:
                needs.append({"from": card["id"], "to": mains[target], "phase": "statement",
                              "statement_walk": typed_walk(by_statement[target], True)})
            else:
                needs.append({"from": card["id"], "to": mains[target], "phase": "proof",
                              "walk": typed_walk(walk, False)})
    needs.sort(key=lambda edge: (edge["from"], edge["to"]))
    graph_of_uses: dict[str, list[str]] = defaultdict(list)
    for edge in uses:
        graph_of_uses[edge["from"]].append(edge["to"])
    clusters = []
    for component in strongly_connected(graph_of_uses):
        if len(component) > 1:
            members = set(component)
            clusters.append({"cards": component,
                             "edges": [[edge["from"], edge["to"]] for edge in uses
                                       if edge["from"] in members and edge["to"] in members],
                             "example_cycle": example_cycle(graph_of_uses, component)})
    unassigned: dict[str, list[str]] = defaultdict(list)
    for path in pages:
        if path not in home and path.split("/")[0] in subjects:
            unassigned[path.rsplit("/", 1)[0]].append(path)
            mentioned.add(path)
    table = {}
    for path in sorted(mentioned):
        about = leaf(path)
        table[path] = {"article_id": about.article_id, "credit": about.credit, "held": about.held,
                       "not_ready": about.not_ready, "stale": about.stale, "state": about.state, "kind": about.kind,
                       "card": home.get(path)}
    return {
        "schema": SCHEMA,
        "commit": commit,
        "cards": sorted(out_cards, key=lambda card: card["id"]),
        "pages": table,
        "uses": uses,
        "needs": needs,
        "clusters": clusters,
        "unassigned": [{"folder": folder, "pages": sorted(found)} for folder, found in sorted(unassigned.items())],
        "edges": dict(sorted(accounting.items())),
        "counts": {"cards": len(out_cards), "pages": len(home), "uses": len(uses), "needs": len(needs),
                   "clusters": len(clusters), "unassigned": sum(len(found) for found in unassigned.values())},
    }


def links_snapshot() -> dict[str, bytes | None]:
    """The files of the links folder that the annotations are read from, each read once, by name: every `*.jsonl`
    file, and the defaults file when there is one, None when it is no regular file, which Autoform cannot use
    (scripts/sync_wiki.py, links_template). An OSError when a file cannot be read."""
    folder = links_dir()
    files: dict[str, bytes | None] = {path.name: path.read_bytes() for path in sorted(folder.glob("*.jsonl"))}
    defaults = folder / LINKS_DEFAULTS
    try:
        found = os.lstat(defaults)
    except FileNotFoundError:
        return files
    except OSError:
        files[LINKS_DEFAULTS] = None
        return files
    files[LINKS_DEFAULTS] = defaults.read_bytes() if stat.S_ISREG(found.st_mode) else None
    return files


def links_digest(files: dict[str, bytes | None]) -> str:
    """The digest of a links folder as read (links_snapshot), which the moves receipt records and hooks/card_pages.py
    recomputes from the files: sha256 over each file, in sorted order of name, as its name, a NUL, its length in bytes
    (`-` for a defaults file that is no regular file), a NUL and its bytes."""
    digest = hashlib.sha256()
    for name in sorted(files):
        data = files[name]
        digest.update(os.fsencode(name) + b"\0" + (b"-" if data is None else str(len(data)).encode()) + b"\0"
                      + (data or b""))
    return digest.hexdigest()


def snapshot_annotations(files: dict[str, bytes | None]) -> dict[Path, dict]:
    """read_annotations, from the bytes of a links folder as read (links_snapshot): each row by the page it is about,
    merged over the template its defaults file gives (scripts/sync_wiki.py, template_of and merged). A ValueError
    names a file that is no UTF-8 JSON lines."""
    if LINKS_DEFAULTS not in files:
        template: dict | None = {}
    else:
        template = None if files[LINKS_DEFAULTS] is None else sync.template_of(files[LINKS_DEFAULTS])
    rows = {}
    for name, data in sorted(files.items()):
        if name == LINKS_DEFAULTS:
            continue
        try:
            annotations = parse_rows(data.decode("utf-8"))
        except ValueError as error:
            raise ValueError(f"{links_dir().name}/{name}: {error}") from error
        for annotation in annotations:
            if (page := sync.subject_of(sync.merged(annotation, template))[0]) is not None:
                rows[page] = annotation
    return rows


def ledger_ids(text: str) -> set[str]:
    """The article ids the ledger's rows name: each page or folder row's `article_id`, and each retirement's `card` or
    `statement` and `replaced_by`; a line that is no JSON object names none (check_moves reports it)."""
    found: set[str] = set()
    for line in text.splitlines():
        try:
            row = json.loads(line) if line.strip() else None
        except ValueError:
            continue
        if isinstance(row, dict):
            found.update(row[key] for key in ("article_id", "card", "statement", "replaced_by")
                         if isinstance(row.get(key), str))
    return found


def final_replacements(text: str) -> dict[tuple[str, str], str]:
    """Each card or statement a retirement row of the ledger ``text`` retires, by kind and id, with the article its
    replacements end at, as check_moves follows them (which has found that they do: at a live card for a card,
    through card retirements; at a live statement page or folder page for a statement, through any retirement)."""
    retired: dict[str, dict[str, str]] = {"card": {}, "statement": {}}
    for line in text.splitlines():
        row = json.loads(line) if line.strip() else None
        for kind, address in (("card", "folder"), ("statement", "page")):
            if isinstance(row, dict) and set(row) == {kind, address, "replaced_by"}:
                retired[kind][row[kind]] = row["replaced_by"]
    finals = {}
    for kind, replaced in retired.items():
        through = retired["card"] if kind == "card" else {**retired["card"], **retired["statement"]}
        for article, at in replaced.items():
            seen = {article}
            while at in through and at not in seen:
                seen.add(at)
                at = through[at]
            finals[(kind, article)] = at
    return finals


def moves(output: Path) -> int:
    """The moves command: check the move ledger, from one read of it and of the links folder, and on success write
    the receipt to ``output`` (see the module's docstring). An id the ledger names that two articles have is an error
    of its own, which check_moves, reading the last of them, would not see; a malformed or repeated id the ledger does
    not name only leaves its card out of the receipt's `cards`."""
    try:
        ledger = moves_file().read_bytes()
    except FileNotFoundError:
        print(f"error: {MOVES}: missing; the moves check certifies a ledger that exists", file=sys.stderr)
        return 1
    try:
        text = ledger.decode("utf-8")
        files = links_snapshot()
        annotations = snapshot_annotations(files)
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    # A row whose extensions are no object holds no card record: card_folders cannot read it.
    cards = card_folders({page: row for page, row in annotations.items()
                          if isinstance(row.get("extensions", {}), dict)})
    holders: dict[str, list[str]] = defaultdict(list)
    for page, row in annotations.items():
        if isinstance(row.get("id"), str):
            holders[row["id"]].append(Path(os.path.relpath(page, wiki.ROADMAP)).as_posix())
    errors = [f"{MOVES}: {article}, which the ledger names, is the id of {len(holders[article])} articles, "
              f"{', '.join(sorted(holders[article]))}; an id names one article"
              for article in sorted(ledger_ids(text)) if len(holders[article]) > 1]
    errors += check_moves(annotations, cards, text=text)
    # The cards the receipt can list: a well-formed id no other article has, and a folder the site can serve, by the
    # predicate hooks/card_pages.py checks the receipt with (valid_address, the same there).
    listed = {card.id: card.node for card in cards.values()
              if isinstance(card.id, str) and ARTICLE_ID.fullmatch(card.id) and len(holders[card.id]) == 1
              and valid_address(card.node)}
    # The live article each retirement ends at, by id, with its kind and node: the hook leads the retired address
    # there, so its address must be one the site can serve, or there is no receipt.
    replacements: dict[str, dict[str, str]] = {}
    if not errors:
        pages = {row["id"]: page for page, row in annotations.items() if isinstance(row.get("id"), str)}
        for (kind, article), final in sorted(final_replacements(text).items()):
            page = pages[final]
            node, what = node_id(page), "folder" if page.name == "README.md" else "page"
            if not valid_address(node):
                errors.append(f"{MOVES}: the retired {kind} {article} is replaced by {final}, whose {what} {node} is "
                              "no address the site serves")
            replacements[final] = {"kind": what, "node": node}
    commit = source_commit()
    if commit is None:
        errors.append(f"{wiki.ROOT} is no Git checkout: the receipt names the commit it checks")
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        return 1
    receipt = {"schema": MOVES_SCHEMA, "commit": commit, "ledger_sha256": hashlib.sha256(ledger).hexdigest(),
               "annotations_sha256": links_digest(files), "cards": listed, "cards_complete": len(listed) == len(cards),
               "replacements": replacements}
    extract.write_whole({output: json.dumps(receipt, ensure_ascii=False, indent=1, sort_keys=True) + "\n"})
    rows = sum(1 for line in text.splitlines() if line.strip())
    print(f"{rows} ledger rows checked; {len(listed)} of {len(cards)} cards listed -> {output}")
    return 0


def option(argv: list[str], name: str) -> tuple[list[str], str | None]:
    """``argv`` without ``name VALUE``, and VALUE (None when absent); a name without a value is a usage error."""
    if name not in argv:
        return argv, None
    at = argv.index(name)
    if at + 1 >= len(argv):
        raise SystemExit(__doc__)
    return argv[:at] + argv[at + 2:], argv[at + 1]


def run(argv: list[str]) -> int:
    if argv[:1] == ["moves"]:
        if len(argv) != 2 or argv[1].startswith("-"):
            print(__doc__, file=sys.stderr)
            return 2
        output = Path(argv[1])
        # Refused as rollup refuses its output, before anything is touched; then an earlier receipt never outlives a
        # failure of this check.
        files = {"OUTPUT": output, "the move ledger": moves_file(),
                 **{f"the links file {path.name}": path for path in sorted(links_dir().glob("*.jsonl"))}}
        if os.path.lexists(links_dir() / LINKS_DEFAULTS):
            files[f"the links file {LINKS_DEFAULTS}"] = links_dir() / LINKS_DEFAULTS
        if problem := extract.file_problem(files, ("OUTPUT",), {"blueprint/": wiki.VAULT}):
            print(f"error: {problem}", file=sys.stderr)
            return 2
        output.unlink(missing_ok=True)
        return moves(output)
    argv, dependency_file = option(argv, "--dependencies")
    argv, base_file = option(argv, "--base-ledger")
    argv, base_links = option(argv, "--base-links")
    argv, renames_file = option(argv, "--renames")
    argv, registry_file = option(argv, "--registry")
    output = Path(argv[1]) if len(argv) == 2 and argv[0] == "rollup" else None
    if output is not None:
        # The output is a file of its own: one inside blueprint/ or the --base-links folder, one that is an input (by
        # its path, a symbolic link or a hard link), a symbolic link itself or no regular file is refused before
        # anything is touched.
        inputs = {"--dependencies": dependency_file, "--registry": registry_file, "--base-ledger": base_file,
                  "--base-links": base_links, "--renames": renames_file}
        files = {"OUTPUT": output, **{flag: Path(given) for flag, given in inputs.items() if given is not None},
                 **{f"the links file {path.name}": path for path in sorted(links_dir().glob("*.jsonl"))}}
        folders = {"blueprint/": wiki.VAULT, **({"--base-links": Path(base_links)} if base_links is not None else {})}
        problem = extract.file_problem(files, ("OUTPUT",), folders)
        if problem:
            print(f"error: {problem}", file=sys.stderr)
            return 2
        # The site shows card data only from a rollup that passed: once the arguments are read, an earlier rollup's
        # file never outlives a failure of this one.
        output.unlink(missing_ok=True)
    if registry_file is not None and dependency_file is None:
        print(__doc__, file=sys.stderr)
        return 2
    if argv not in (["check"],) and not (output is not None and dependency_file is not None):
        print(__doc__, file=sys.stderr)
        return 2
    history = (base_file, base_links, renames_file)
    if any(option is not None for option in history) and not all(option is not None for option in history):
        # Half a history would check the ledger's prefix and skip the moves since the base commit.
        print("error: --base-ledger, --base-links and --renames go together", file=sys.stderr)
        return 2
    loaded = {}
    for flag, given in (("--dependencies", dependency_file), ("--registry", registry_file)):
        if given is None:
            continue
        try:
            loaded[flag] = json.loads(Path(given).read_text())
        except (OSError, ValueError) as error:
            print(f"error: {flag} {given}: {error}", file=sys.stderr)
            return 1
        # A file given is checked whatever it holds: JSON `null` is no run without it.
        if not isinstance(loaded[flag], dict):
            print(f"error: {flag} {given} holds no JSON object; extract_v2_lean_dependencies.py writes it",
                  file=sys.stderr)
            return 1
    dependencies, registry = loaded.get("--dependencies"), loaded.get("--registry")
    # A registry of the extractor's form, before anything reads its tables, made beside the extraction given: the
    # two are valid only as the pair one extractor run wrote.
    if registry is not None and (problems := sync.registry_form_problems(registry)
                                 or sync.extraction_problems(registry, Path(dependency_file))):
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 1
    base = None if base_file is None else Path(base_file).read_text()
    base_annotations = None if base_links is None else read_links(Path(base_links))
    renames = None if renames_file is None else read_renames(Path(renames_file))
    # Rows Autoform would read otherwise, or not at all, which rows by page cannot show, are refused first, as
    # extraction and the sync refuse them.
    rows = {path: parse_rows(path.read_text()) for path in sorted(links_dir().glob("*.jsonl"))}
    problems = sync.credit_problems(rows) + sync.pageless_rows(rows)
    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 1
    annotations = read_annotations()
    committed = committed_annotations()
    cards = card_folders(annotations)
    graph = load_graph() if cards or dependencies is not None else None
    errors, warnings = check(annotations, graph, committed, dependencies, base, base_annotations, renames, registry)
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    print(f"{len(cards)} cards, {sum(len(leaves(folder)) for folder in cards)} statement pages in them; "
          f"{len(errors)} errors, {len(warnings)} warnings")
    if errors or argv[0] == "check":
        return 1 if errors else 0
    result = rollup(dependencies, annotations, graph, committed, source_commit(), checked=True, registry=registry)
    # Written whole or not at all, through a temporary file of a name no file has.
    extract.write_whole({output: json.dumps(result, ensure_ascii=False, indent=1, sort_keys=True) + "\n"})
    counts = result["counts"]
    print(f"{counts['uses']} card edges, {counts['needs']} main-statement edges, {counts['clusters']} cyclic clusters, "
          f"{counts['unassigned']} statement pages in no card of their subjects")
    return 0


if __name__ == "__main__":
    sys.exit(run(sys.argv[1:]))
