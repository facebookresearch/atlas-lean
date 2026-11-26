#!/usr/bin/env python3
"""Pages for Mathlib's declarations, built from the Mathlib layer of the dependency graph.

    python scripts/build_mathlib_pages.py build [--strict-links] [--report REPORT.json] SITE GRAPH OUT
    python scripts/build_mathlib_pages.py check SITE GRAPH OUT
    python scripts/build_mathlib_pages.py moves (--base REV | --at COMMIT) (--graph GRAPH | --modules LIST)
        [--write SLUG [--now YYYYMMDDTHHMMSSZ]]
    python scripts/build_mathlib_pages.py check-moves --base REV (--graph GRAPH | --modules LIST)

`build` reads a built site (the `site` directory the wiki job builds) and the `mathlib-graph` artifact of the same
ATLAS revision (docs/mathlib-layer.md), and writes OUT: the same site plus one page per Mathlib module under
`mathlib/`, grouped by the topics of scripts/taxonomy.json, with the site's links to Mathlib declarations pointed
at those pages and each statement box listing the Mathlib declarations its Lean statement and proof use. `check`
verifies OUT against SITE: every file of SITE is in OUT, unchanged apart from the links and additions `build`
makes, and every link `build` writes resolves to the declaration it names. docs/mathlib-pages.md describes the
pages and the link scheme.

Module pages never move; index pages move when the taxonomy changes. The record of scripts/mathlib-moves.d says where
some of them went: `build` writes a notice at each recorded route that no page holds, and `check` checks the notices
both ways and, on a pull request, its new rows. `moves` proposes rows for the index routes a change removes and writes
them to a new fragment; `check-moves` judges the head commit's new rows as a pull request's check does, for a pull
request that changes the record alone, which the workflow does not build: with --graph a verification of record (exit
0, 1, or 4 when the record cannot be established), with --modules advice (exit 3)
(docs/mathlib-pages.md#moved-index-pages).

The pages' chrome (header, navigation, footer) comes from MkDocs with the site's own theme: MkDocs renders a
placeholder page for each Mathlib page and the declarations are put in afterwards, since MkDocs would take hours
over the declarations themselves. Nothing this script writes is committed.
"""

from __future__ import annotations

import argparse
import collections
import functools
import gzip
import hashlib
import html
import importlib.util
import inspect
import io
import json
import math
import os
import posixpath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as etree
import zipfile
from collections.abc import Collection, Iterable
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from types import ModuleType, SimpleNamespace
from urllib.parse import quote, unquote_to_bytes, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))
from card_moves import content_problem, name_problem  # noqa: E402  (the fragments' rules, docs/cards.md)

ROOT = Path(__file__).resolve().parent.parent
TAXONOMY = ROOT / "scripts" / "taxonomy.json"
STYLESHEET = ROOT / "scripts" / "mathlib_pages.css"
SECTION = "mathlib"
STYLESHEET_PATH = "stylesheets/mathlib.css"
SEARCH_INDEX = "search/search_index.json"
MATHLIB_GIT = "https://github.com/leanprover-community/mathlib4"
DOCS_FIND = "https://leanprover-community.github.io/mathlib4_docs/find/?pattern="
# How many users a declaration lists, and how many Mathlib declarations a statement box lists per kind; the
# counts beside them always cover all of them.
USERS_SHOWN = 20
ATLAS_SHOWN = 20
CARD_SHOWN = 40
# A declaration's anchor is its name. Every other id on a Mathlib page starts with "_", which no node's name does:
# docs/mathlib-layer.md drops names with a part that starts with "_".
SLOT = '<div class="_ml-slot"></div>'

DOCS_HREF = re.compile(r"https://leanprover-community\.github\.io/mathlib4_docs/find/\?pattern=([^#]*)#doc")
SOURCE_HREF = re.compile(re.escape(MATHLIB_GIT) + r"/blob/[0-9a-f]{40}/[^#]+\.lean#L[1-9][0-9]*")
A_TAG = re.compile(r"<a\s[^>]*>")
ATTRIBUTE = re.compile(r'\s([^\s"\'>/=]+)(?:="([^"]*)")?')
CARD_TAG = re.compile(r'<div class="bp-thmwrapper[ "][^>]*>')
DIV_TOKEN = re.compile(r"<div\b|</div>")
DETAILS = re.compile(r'<details class="bp-dependencies">(.*?)</details>', re.DOTALL)
META_MATHLIB = re.compile(r'<span class="bp-key">Mathlib</span><span class="bp-value">(<code>([^<]*)</code>)')
HEADING = re.compile(r'<h[1-6]\b[^>]*>')
READING_SOURCE = re.compile(r'<div class="bp-reading-source" data-autoform-node-id="([^"]*)"')
# Autoform's split of a `lean:` value into declaration names (lean.declaration_names).
DECLARATION_NAME = re.compile(r"(?:«[^»]*(?:»|$)|[^\s,«])+")
LEAN_BLOCK = re.compile(r'<pre class="bp-lean">.*?</pre>', re.DOTALL)
HOME_ANCHOR = '<div class="bp-hero-coverage">'


def jsonl(path: Path):
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        for line in handle:
            yield json.loads(line)


def slugify(text: str, limit: int = 48) -> str:
    """The folder name scripts/generate_wiki.py gives a topic of this title."""
    slug = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return slug[:limit].rstrip("-") or "untitled"


def fragment(name: str) -> str:
    return quote(name, safe="")


def esc(text: str) -> str:
    return html.escape(text, quote=True)


def relative(target: str, source: str) -> str:
    """The relative URL of the site path `target` from the page at the site path `source`."""
    return posixpath.relpath(target, posixpath.dirname(source) or ".")


def decoded(percent: str) -> str | None:
    try:
        return unquote_to_bytes(percent).decode("utf-8", "strict")
    except UnicodeDecodeError:
        return None


def count(n: int, noun: str) -> str:
    return f"{n:,} {noun}{'' if n == 1 else 's'}"


def nav_text(text: str) -> str:
    """A title as the link text of a SUMMARY.md entry, which literate-nav reads as Markdown and the theme writes
    as HTML. The title's own `&`, `<` and `>` become character references, so that none of it reads as markup, and
    so do its brackets, which Python-Markdown would otherwise take, `]:` say, for a reference definition before it
    reads a backslash."""
    text = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("[", "&#91;")
    return re.sub(r"([\\`*_#!|$])", r"\\\1", text.replace("]", "&#93;"))


# ---------------------------------------------------------------------------------------------------------------
# Inputs


@dataclass
class Graph:
    """The Mathlib layer: nodes, their topics, statement and proof edges, and ATLAS's bridge edges."""

    rev: str
    atlas_commit: str
    names: list[str]
    index: dict[str, int]
    module: list[str]
    kind: list[str]
    name_line: list[int]
    doc: list[str]
    signature: list[str]
    instance: list[bool]
    topic: list[tuple[str, str] | None]
    outside: dict[str, str]
    statement: list[list[int]]
    proof: list[list[int]]
    users: list[list[tuple[int, str]]]
    bridge: dict[str, tuple[list[int], list[int]]]
    bridge_users: list[list[tuple[str, str]]]

    def source(self, i: int) -> str:
        """The address of the line of the declaration's name at the pinned revision."""
        return f"{MATHLIB_GIT}/blob/{self.rev}/{self.module[i].replace('.', '/')}.lean#L{self.name_line[i]}"


def load_graph(directory: Path) -> Graph:
    versions = json.loads((directory / "stats.json").read_text(encoding="utf-8"))["versions"]
    rev, atlas_commit = versions.get("mathlib_rev") or "", versions.get("atlas_commit") or ""
    for value in (rev, atlas_commit):
        if not re.fullmatch(r"[0-9a-f]{40}", value):
            raise SystemExit(f"{directory}/stats.json: revision {value!r} is not a full commit")
    names, module, kind, name_line, doc, signature = [], [], [], [], [], []
    for row in jsonl(directory / "nodes.jsonl.gz"):
        names.append(row["name"])
        module.append(row["module"])
        kind.append(row["kind"])
        name_line.append(int(row["name_line"]))
        doc.append(row.get("doc") or "")
        signature.append(row.get("signature") or "")
    index = {name: i for i, name in enumerate(names)}
    if len(index) != len(names):
        raise SystemExit(f"{directory}/nodes.jsonl.gz: names are not unique")
    size = len(names)
    topic: list[tuple[str, str] | None] = [None] * size
    outside: dict[str, str] = {}
    for row in jsonl(directory / "topics.jsonl.gz"):
        i = index[row["name"]]
        if row.get("to"):
            topic[i] = (row["to"], row["title"])
        else:
            outside[module[i]] = row.get("exclude") or "not placed in the taxonomy"
    statement: list[set[int]] = [set() for _ in range(size)]
    proof: list[set[int]] = [set() for _ in range(size)]
    for row in jsonl(directory / "edges.jsonl.gz"):
        (statement if row["kind"] == "statement" else proof)[index[row["source"]]].add(index[row["target"]])
    users: list[list[tuple[int, str]]] = [[] for _ in range(size)]
    for source in range(size):
        for target in statement[source]:
            users[target].append((source, "statement"))
        for target in proof[source] - statement[source]:
            users[target].append((source, "proof"))
    bridge_sets: dict[str, tuple[set[int], set[int]]] = {}
    for row in jsonl(directory / "bridge-edges.jsonl.gz"):
        entry = bridge_sets.setdefault(row["source"], (set(), set()))
        entry[0 if row["kind"] == "statement" else 1].add(index[row["target"]])

    def by_name(targets):
        return sorted(targets, key=lambda i: names[i])

    bridge = {article: (by_name(s), by_name(p - s)) for article, (s, p) in sorted(bridge_sets.items())}
    bridge_users: list[list[tuple[str, str]]] = [[] for _ in range(size)]
    for article, (s, p) in bridge.items():
        for target in s:
            bridge_users[target].append((article, "statement"))
        for target in p:
            bridge_users[target].append((article, "proof"))
    return Graph(
        rev=rev,
        atlas_commit=atlas_commit,
        names=names,
        index=index,
        module=module,
        kind=kind,
        name_line=name_line,
        doc=doc,
        signature=signature,
        instance=[k == "instance" for k in kind],
        topic=topic,
        outside=outside,
        statement=[by_name(s) for s in statement],
        proof=[by_name(p - s) for s, p in zip(statement, proof)],
        users=users,
        bridge=bridge,
        bridge_users=bridge_users,
    )


@dataclass
class Article:
    id: str
    lean: list[str]
    path: str
    anchor: str  # empty for an article that is its own page
    title: str
    status: str

    def href(self, here: str) -> str:
        return relative(self.path, here) + (f"#{self.anchor}" if self.anchor else "")


@dataclass
class Site:
    """What the built site publishes about ATLAS, from its publication manifest and the explorer's catalog: the
    revision; the folders whose pages the site has; and the articles whose statement box the site has exactly once
    where the catalog says, on the route's page with the route's anchor as its heading, by id and by Lean name."""

    commit: str
    articles: dict[str, Article]
    by_lean: dict[str, list[Article]]
    scopes: dict[str, tuple[str, str]]
    pages: list[str]
    unpublished: int


def boxes(page: str):
    """Each statement box of a page: its start, its end, its article id and the id of its own statement heading, the
    box's first heading (None when that is not a statement heading with an id)."""
    for start, end, node_id in statement_boxes(page):
        heading = HEADING.search(page, start, end)
        attrs = attributes(heading.group()) if heading else {}
        own = "bp-thmheading" in attrs.get("class", "").split() and "id" in attrs
        yield start, end, node_id, attrs["id"] if own else None


def read_site(site: Path) -> Site:
    publication = json.loads((site / "publication.json").read_text(encoding="utf-8"))
    catalog = json.loads((site / "dependencies" / "index.json").read_text(encoding="utf-8"))
    pages = sorted(path.relative_to(site).as_posix() for path in site.rglob("*.html"))
    published = set(pages)
    found: dict[str, collections.Counter] = {}
    ids: dict[str, collections.Counter] = {}
    articles: dict[str, Article] = {}
    by_lean: dict[str, list[Article]] = collections.defaultdict(list)
    scopes: dict[str, tuple[str, str]] = {}
    unpublished = 0
    for node in catalog["nodes"]:
        target = urlsplit(node["route"])
        path = posixpath.normpath(posixpath.join("dependencies", target.path))
        if path not in published:
            unpublished += node["kind"] != "scope"
            continue
        if node["kind"] == "scope":
            scopes[node["id"]] = (path, node["title"])
            continue
        if path not in found:
            page = (site / path).read_text(encoding="utf-8")
            found[path] = collections.Counter((node_id, anchor) for _, _, node_id, anchor in boxes(page))
            # An article that is its own page: its route has no anchor.
            found[path].update((node_id, "") for node_id in READING_SOURCE.findall(page))
            ids[path] = collections.Counter(html.unescape(x) for x in IDS.findall(page))
        # The route's anchor must be the box's own heading and no other element's id.
        if found[path][(node["id"], target.fragment)] != 1 or (target.fragment and ids[path][target.fragment] != 1):
            unpublished += 1
            continue
        names = DECLARATION_NAME.findall(node.get("lean") or "")
        article = Article(node["id"], names, path, target.fragment, node["title"], node["status"])
        articles[article.id] = article
        for name in dict.fromkeys(names):
            by_lean[name].append(article)
    return Site(publication.get("git_ref") or "", articles, dict(by_lean), scopes, pages, unpublished)


def canonical(info: Site, path: str, node_id: str, anchor: str | None) -> Article | None:
    """The article of a statement box when the box is that article's published one."""
    article = info.articles.get(node_id)
    if article is None or not article.anchor or (article.path, article.anchor) != (path, anchor):
        return None
    return article


def article_uses(graph: Graph, article: Article) -> tuple[list[int], list[int]]:
    """The Mathlib declarations an article's Lean names use in their statements, and only in their proofs."""
    statement: dict[int, None] = {}
    proof: dict[int, None] = {}
    for name in article.lean:
        uses = graph.bridge.get(name, ((), ()))
        statement.update(dict.fromkeys(uses[0]))
        proof.update(dict.fromkeys(uses[1]))
    ordered = sorted(statement, key=lambda i: graph.names[i])
    return ordered, sorted((i for i in proof if i not in statement), key=lambda i: graph.names[i])


def taxonomy_tree(taxonomy: dict) -> tuple[dict[str, str], dict[str, str], list[str], dict[str, set[str]]]:
    """Titles and descriptions of subjects, fields and subfields by path, their order, and each field's subfield
    folder names."""
    titles: dict[str, str] = {}
    descriptions: dict[str, str] = {}
    order: list[str] = []
    subfields: dict[str, set[str]] = collections.defaultdict(set)
    for subject, spec in taxonomy["subjects"].items():
        titles[subject], descriptions[subject] = spec["title"], spec.get("description", "")
        order.append(subject)
        for item in spec.get("fields", []):
            path = f"{subject}/{item['slug']}"
            titles[path], descriptions[path] = item["title"], item.get("description", "")
            order.append(path)
            subfields[subject].add(item["slug"])
            for sub in item.get("subfields", []):
                subpath = f"{path}/{sub['slug']}"
                titles[subpath], descriptions[subpath] = sub["title"], sub.get("description", "")
                order.append(subpath)
                subfields[path].add(sub["slug"])
    return titles, descriptions, order, subfields


# ---------------------------------------------------------------------------------------------------------------
# The page plan


@dataclass
class Page:
    path: str  # site path of the HTML file
    title: str  # the page's title and heading
    nav: str  # its entry in the navigation
    kind: str  # home, group (subject, field or subfield), topic, module or outside
    modules: list[str] = field(default_factory=list)
    children: list["Page"] = field(default_factory=list)
    taxonomy: str = ""  # a group's path in the taxonomy
    topic: tuple[str, str] | None = None


@dataclass
class Plan:
    home: Page
    pages: list[Page]
    page_of_module: dict[str, Page]
    members: dict[str, list[int]]


def module_path(module: str) -> str:
    return f"{SECTION}/{module.removeprefix('Mathlib.')}.html"


def plan_pages(graph: Graph, hosted: set[int], taxonomy: dict, reserved: Collection[str] = frozenset()) -> Plan:
    """One page per module with hosted declarations; one per topic with several such modules, else the module's
    page stands for its topic; one per subject, field and subfield; modules outside the taxonomy on their own.
    ``reserved``: the routes the record of moved index pages holds (MoveRecord), topics' and groups' alike, which no
    topic takes; a scope still has its page at its path. A topic's folder is its natural slug, unless a folder of its
    scope, a recorded route or a topic before it in order has it; then the next of -2, -3, ... that none of these and
    no other topic's natural slug has, so that no topic takes a route its owner keeps. The record's tools call a
    commit's own plan_pages, with ``reserved`` when that version takes it, so its name stays."""
    titles, _, order, subfields = taxonomy_tree(taxonomy)
    members: dict[str, list[int]] = collections.defaultdict(list)
    for i in sorted(hosted, key=lambda i: (graph.module[i], graph.name_line[i], graph.names[i])):
        members[graph.module[i]].append(i)
    topic_modules: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
    outside_modules: list[str] = []
    for module in sorted(members):
        topics = {graph.topic[i] for i in members[module]}
        if len(topics) != 1:
            raise SystemExit(f"{module}: its declarations have different topics")
        (topic,) = topics
        (outside_modules if topic is None else topic_modules[topic]).append(module)
    home = Page(f"{SECTION}/index.html", "Mathlib", "Mathlib", "home")
    pages = [home]
    page_of_module: dict[str, Page] = {}
    groups: dict[str, Page] = {}

    def group(path: str) -> Page:
        if path not in groups:
            parent = group(path.rsplit("/", 1)[0]) if "/" in path else home
            title = titles.get(path, path)
            groups[path] = Page(f"{SECTION}/{path}/index.html", title, title, "group", taxonomy=path)
            parent.children.append(groups[path])
            pages.append(groups[path])
        return groups[path]

    def add_module(parent: Page, module: str, title: str, topic) -> None:
        page = Page(module_path(module), title, title, "module", [module], topic=topic)
        parent.children.append(page)
        pages.append(page)
        page_of_module[module] = page

    rank = {path: n for n, path in enumerate(order)}
    for to in sorted({to for to, _ in topic_modules}, key=lambda to: (rank.get(to, len(rank)), to)):
        container = group(to)
        topics = sorted((t for t in topic_modules if t[0] == to), key=lambda t: (t[1].casefold(), t[1]))
        own = [topic for topic in topics if len(topic_modules[topic]) > 1]
        folders = set(subfields.get(to, ()))
        slugs: dict[tuple[str, str], str] = {}
        for topic in own:
            slug = slugify(topic[1])
            if slug not in folders and f"{to}/{slug}" not in reserved and slug not in slugs.values():
                slugs[topic] = slug
        taken = folders | set(slugs.values())
        for topic in own:
            if topic not in slugs:
                number = 2
                while (slug := f"{slugify(topic[1])}-{number}") in taken or f"{to}/{slug}" in reserved:
                    number += 1
                slugs[topic] = slug
                taken.add(slug)
        for topic in topics:
            modules = topic_modules[topic]
            if len(modules) == 1:
                add_module(container, modules[0], topic[1], topic)
                continue
            page = Page(f"{SECTION}/{to}/{slugs[topic]}/index.html", topic[1], topic[1], "topic", modules, topic=topic)
            container.children.append(page)
            pages.append(page)
            for module in modules:
                add_module(page, module, module, topic)
    if outside_modules:
        page = Page(f"{SECTION}/outside/index.html", "Modules outside the taxonomy", "Outside the taxonomy",
                    "outside", outside_modules)
        home.children.append(page)
        pages.append(page)
        for module in outside_modules:
            add_module(page, module, module, None)
    for page in pages:
        page.children.sort(key=lambda c: (c.kind != "group", rank.get(c.taxonomy, len(rank)) * (c.kind == "group")))
    if len({page.path for page in pages}) != len(pages):
        raise SystemExit("two Mathlib pages have the same path")
    return Plan(home, pages, page_of_module, dict(members))


# ---------------------------------------------------------------------------------------------------------------
# Content


class Docstrings:
    """Docstrings as HTML: Markdown with code blocks and formulas as the site writes them, no raw HTML, links kept
    only to http, https and mailto addresses, and a name in code that is a declaration with a page linked to it."""

    def __init__(self, resolve):
        import markdown
        from markdown.extensions import Extension
        from markdown.treeprocessors import Treeprocessor

        class Clean(Treeprocessor):
            def run(self, root):
                for element in list(root.iter()):
                    if element.tag == "a" and urlsplit(element.get("href", "")).scheme.lower() not in {
                        "http", "https", "mailto"
                    }:
                        element.tag = "span"
                        element.attrib.clear()
                    elif element.tag == "img":
                        alt = element.get("alt", "")
                        element.tag = "span"
                        element.attrib.clear()
                        element.text = alt
                    elif element.tag == "code" and element.text and len(element) == 0:
                        href = resolve(element.text.strip())
                        if href:
                            link = etree.SubElement(element, "a", {"href": href})
                            link.text, element.text = element.text, None
                return root

        class NoHtml(Extension):
            def extendMarkdown(self, md):
                md.preprocessors.deregister("html_block")
                md.inlinePatterns.deregister("html")
                md.treeprocessors.register(Clean(md), "mathlib-clean", 0)

        self.markdown = markdown.Markdown(
            extensions=["fenced_code", "tables", "pymdownx.arithmatex", NoHtml()],
            extension_configs={"pymdownx.arithmatex": {"generic": True}},
        )

    def __call__(self, text: str) -> str:
        self.markdown.reset()
        return self.markdown.convert(text)


@dataclass
class Context:
    graph: Graph
    site: Site
    plan: Plan
    hosted: set[int]
    credits: dict[int, list[Article]]
    atlas_topics: dict[tuple[str, str], tuple[str, str]]
    here: str = ""

    def page_of(self, i: int) -> str | None:
        return self.plan.page_of_module[self.graph.module[i]].path if i in self.hosted else None

    def href(self, i: int, here: str | None = None) -> str | None:
        here = self.here if here is None else here
        page = self.page_of(i)
        if page is None:
            return None
        anchor = "#" + fragment(self.graph.names[i])
        return anchor if page == here else relative(page, here) + anchor

    def link(self, i: int, here: str | None = None) -> str:
        """The address of a declaration: its page, or its pinned source line when this build has no page for it."""
        return self.href(i, here) or self.graph.source(i)

    def ref(self, i: int) -> str:
        return f'<a href="{esc(self.link(i))}">{esc(self.graph.names[i])}</a>'


def render_declaration(ctx: Context, i: int, docs: Docstrings) -> str:
    graph = ctx.graph
    name = graph.names[i]
    signature = graph.signature[i]
    if signature.startswith(name):
        signature = signature[len(name):].lstrip()
    parts = [
        f'<div class="ml-decl" id="{esc(name)}">',
        f'<p class="ml-head"><span class="ml-kind">{esc(graph.kind[i])}</span> '
        f'<a class="ml-name" href="#{esc(fragment(name))}">{esc(name)}</a> '
        f'<a class="ml-src" href="{esc(graph.source(i))}">source</a></p>',
    ]
    if signature:
        parts.append(f'<pre class="ml-sig"><code>{esc(signature)}</code></pre>')
    if graph.doc[i]:
        parts.append(f'<div class="ml-doc">{docs(graph.doc[i])}</div>')
    for label, targets in (("Statement uses", graph.statement[i]), ("Proof uses", graph.proof[i])):
        if not targets:
            continue
        text = ", ".join(ctx.ref(t) for t in targets if not graph.instance[t])
        instances = [f"<code>{esc(graph.names[t])}</code>" for t in targets if graph.instance[t]]
        if instances:
            text += ("; " if text else "") + f'<span class="ml-inst">instances: {", ".join(instances)}</span>'
        parts.append(f'<p class="ml-uses"><b>{label}</b> {text}</p>')
    users = graph.users[i]
    if users:
        ordered = sorted(users, key=lambda u: (u[1] != "statement", graph.instance[u[0]], -len(graph.users[u[0]]),
                                               graph.names[u[0]]))
        in_statements = sum(1 for _, kind in users if kind == "statement")
        tally = [count(in_statements, "statement")] if in_statements else []
        tally += [count(len(users) - in_statements, "proof")] if len(users) > in_statements else []
        more = len(users) - USERS_SHOWN
        text = ", ".join(ctx.ref(u) for u, _ in ordered[:USERS_SHOWN]) + (f" and {more:,} more" if more > 0 else "")
        parts.append(f'<p class="ml-used"><b>Used by</b> {", ".join(tally)}: {text}</p>')
    kinds: dict[str, str] = {}
    for name, kind in graph.bridge_users[i]:
        for article in ctx.site.by_lean.get(name, ()):
            if kinds.get(article.id) != "statement":
                kinds[article.id] = kind
    if kinds:
        articles = sorted(((ctx.site.articles[a], kind) for a, kind in kinds.items()),
                          key=lambda x: (x[1] != "statement", x[0].title.casefold(), x[0].id))
        in_statements = sum(1 for _, kind in articles if kind == "statement")
        tally = [count(in_statements, "statement")] if in_statements else []
        tally += [count(len(articles) - in_statements, "proof")] if len(articles) > in_statements else []
        more = len(articles) - ATLAS_SHOWN
        text = ", ".join(f'<a href="{esc(a.href(ctx.here))}">{esc(a.title)}</a>' for a, _ in articles[:ATLAS_SHOWN])
        parts.append(f'<p class="ml-atlas"><b>Used in ATLAS by</b> {", ".join(tally)}: {text}'
                     + (f" and {more:,} more" if more > 0 else "") + "</p>")
    credited = ctx.credits.get(i)
    if credited:
        text = ", ".join(f'<a href="{esc(a.href(ctx.here))}">{esc(a.title)}</a>' for a in credited)
        parts.append(f'<p class="ml-credit"><b>Stated in ATLAS as</b> {text}</p>')
    parts.append("</div>")
    return "".join(parts)


def atlas_line(ctx: Context, found: tuple[str, str] | None) -> str:
    if not found:
        return ""
    href = relative(found[0], ctx.here)
    return f'<p class="ml-meta">In the ATLAS roadmap: <a href="{esc(href)}">{esc(found[1])}</a></p>'


def render_module(ctx: Context, page: Page, docs: Docstrings) -> str:
    graph = ctx.graph
    module = page.modules[0]
    indices = ctx.plan.members[module]
    source = f"{MATHLIB_GIT}/blob/{graph.rev}/{module.replace('.', '/')}.lean"
    meta = [f"Module <code>{esc(module)}</code>", f'<a href="{esc(source)}">source</a>',
            count(len(indices), "declaration")]
    if module in graph.outside:
        meta.append(f"outside the taxonomy: {esc(graph.outside[module])}")
    parts = [f'<p class="ml-meta">{" · ".join(meta)}</p>', atlas_line(ctx, ctx.atlas_topics.get(page.topic))]
    parts.extend(render_declaration(ctx, i, docs) for i in indices)
    return "".join(parts)


def render_index(ctx: Context, page: Page, descriptions: dict[str, str], below: dict[str, list[str]]) -> str:
    parts = []
    if page.kind == "home":
        parts.append(
            "<p>Every Mathlib declaration a mathematician could cite, at the revision of Mathlib this project builds "
            "against: its statement, its documentation, the declarations its statement and its proof use, the "
            "declarations that use it, and the ATLAS statements that use it. Pages follow the topics of the ATLAS "
            "roadmap, one page per Mathlib module.</p>"
        )
        parts.append(
            f'<p class="ml-meta">Mathlib <a href="{esc(MATHLIB_GIT)}/tree/{esc(ctx.graph.rev)}">'
            f"<code>{esc(ctx.graph.rev[:12])}</code></a> · {count(len(ctx.hosted), 'declaration')} · "
            f"{count(len(ctx.plan.members), 'module')}</p>"
        )
    elif page.kind == "group":
        if descriptions.get(page.taxonomy):
            parts.append(f"<p>{esc(descriptions[page.taxonomy])}</p>")
        parts.append(atlas_line(ctx, ctx.site.scopes.get(page.taxonomy)))
    elif page.kind == "topic":
        parts.append(atlas_line(ctx, ctx.atlas_topics.get(page.topic)))
    items = []
    for child in page.children:
        modules = below[child.path]
        size = sum(len(ctx.plan.members[m]) for m in modules)
        counts = count(size, "declaration")
        if child.kind != "module":
            counts = f"{count(len(modules), 'module')}, {counts}"
        reason = f" ({esc(ctx.graph.outside.get(child.modules[0], ''))})" if page.kind == "outside" else ""
        items.append(f'<li><a href="{esc(relative(child.path, ctx.here))}">{esc(child.nav)}</a> '
                     f'<span class="ml-count">{counts}</span>{reason}</li>')
    if items:
        parts.append(f'<ul class="ml-list">{"".join(items)}</ul>')
    return "".join(parts)


def modules_below(plan: Plan) -> dict[str, list[str]]:
    below: dict[str, list[str]] = {}

    def walk(page: Page) -> list[str]:
        found = dict.fromkeys(page.modules if page.kind == "module" else [])
        for child in page.children:
            found.update(dict.fromkeys(walk(child)))
        below[page.path] = list(found)
        return below[page.path]

    walk(plan.home)
    return below


# ---------------------------------------------------------------------------------------------------------------
# Chrome: MkDocs renders a placeholder for every page with the site's theme


def summary_markdown(plan: Plan) -> str:
    lines = ["- [Home](index.md)"]

    def emit(page: Page, depth: int) -> None:
        lines.append("    " * depth + f"- [{nav_text(page.nav)}]({page.path[: -len('.html')]}.md)")
        for child in page.children:
            emit(child, depth + 1)

    emit(plan.home, 0)
    return "\n".join(lines) + "\n"


def render_chrome(plan: Plan, work: Path, mkdocs: list[str]) -> tuple[dict[str, str], list[dict]]:
    import yaml  # MkDocs' own YAML library, which reads the stubs' front matter

    docs, built = work / "docs", work / "site"
    docs.mkdir(parents=True)
    (docs / "index.md").write_text("Home\n", encoding="utf-8")
    for page in plan.pages:
        stub = docs / f"{page.path[: -len('.html')]}.md"
        stub.parent.mkdir(parents=True, exist_ok=True)
        # The theme writes the title into the page's head and header as HTML, so its `&`, `<` and `>` go in
        # escaped; other titles, the ones with an apostrophe say, read as before. YAML writes it, escaping what
        # YAML cannot hold as such, a control character say, which would leave the front matter unread.
        front = yaml.safe_dump({"title": html.escape(page.title, quote=False)}, allow_unicode=True, width=2**31)
        stub.write_text(f"---\n{front}---\n\n"
                        f'<h1 id="_title">{esc(page.title)}</h1>\n\n{SLOT}\n', encoding="utf-8")
    (docs / "SUMMARY.md").write_text(summary_markdown(plan), encoding="utf-8")
    config = work / "mkdocs.yml"
    config.write_text("\n".join([
        f"INHERIT: {json.dumps(str(ROOT / 'mkdocs.yml'))}",
        f"docs_dir: {json.dumps(str(docs))}",
        f"site_dir: {json.dumps(str(built))}",
        "theme:",
        "  name: material",
        f"  custom_dir: {json.dumps(str(ROOT / 'theme'))}",
        "hooks:",
        f"  - {json.dumps(str(ROOT / 'hooks' / 'title_only_search.py'))}",
        f"  - {json.dumps(str(ROOT / 'hooks' / 'trim_pages.py'))}",
        "extra_css:",
        "  - stylesheets/blueprint.css",
        f"  - {STYLESHEET_PATH}",
        "",
    ]), encoding="utf-8")
    subprocess.run([*mkdocs, "build", "--strict", "--quiet", "--config-file", str(config)], check=True)
    pages: dict[str, str] = {}
    for page in plan.pages:
        text = (built / page.path).read_text(encoding="utf-8")
        if text.count(SLOT) != 1:
            raise SystemExit(f"{page.path}: the theme did not keep the page's placeholder exactly once")
        pages[page.path] = text
    index = json.loads((built / SEARCH_INDEX).read_text(encoding="utf-8"))
    return pages, [doc for doc in index["docs"] if doc["location"].startswith(f"{SECTION}/")]


# ---------------------------------------------------------------------------------------------------------------
# The ATLAS pages: links to Mathlib declarations, and the declarations each statement box uses


def docs_href(name: str) -> str:
    """The address Autoform gives a constant's page in Mathlib's documentation."""
    return DOCS_FIND + quote(name, safe=".") + "#doc"


def raw_href(tag: str) -> str:
    """A start tag's href as written, entities and all."""
    match = re.search(r'\shref="([^"]*)"', tag)
    return match.group(1) if match else ""


def attributes(tag: str) -> dict[str, str]:
    return {key: html.unescape(value or "") for key, value in ATTRIBUTE.findall(tag[2:-1])}


def with_href(tag: str, href: str, marker: str) -> str:
    """The start tag `tag` with its href replaced and marked, so that `check` can restore it."""
    start = tag.index(' href="') + len(' href="')
    end = tag.index('"', start)
    return f'{tag[:start]}{esc(href)}{tag[end:-1]} data-ml="{marker}">'


def card_end(page: str, start: int) -> int:
    """The end of the statement box whose start tag is at `start`."""
    depth = 0
    for token in DIV_TOKEN.finditer(page, start):
        depth += 1 if token.group() == "<div" else -1
        if depth == 0:
            return token.end()
    raise ValueError("a statement box is not closed")


def statement_boxes(page: str):
    """Each statement box of a page: its start, its end and its article id."""
    at = 0
    for match in CARD_TAG.finditer(page):
        if match.start() < at:
            continue
        at = card_end(page, match.start())
        yield match.start(), at, attributes(match.group()).get("data-autoform-node-id", "")


class Enricher:
    def __init__(self, ctx: Context):
        self.ctx = ctx
        self.report: collections.Counter = collections.Counter()
        self.problems: list[str] = []

    def links(self, page: str, path: str) -> str:
        """Article source links anywhere, and Autoform's documentation links in its Lean blocks, pointed at the
        Mathlib pages; only links spelled exactly as their scheme writes them, so that `check` can restore them."""
        graph = self.ctx.graph
        if 'data-ml="' in page and any(" data-ml=" in tag.group() for tag in A_TAG.finditer(page)):
            raise SystemExit(f"{path}: the site already has a link marked as a Mathlib page link")

        def source(match: re.Match) -> str:
            tag = match.group()
            href = raw_href(tag)
            if not href.startswith(MATHLIB_GIT + "/blob/"):
                return tag
            attrs = attributes(tag)
            if "title" not in attrs or not SOURCE_HREF.fullmatch(html.unescape(href)):
                return tag
            i = graph.index.get(attrs["title"])
            if i is None or href != esc(graph.source(i)):
                self.problems.append(f"{path}: a Mathlib source link titled {attrs['title']!r} is not that "
                                     "declaration's source link at the pinned revision")
                self.report["source links that do not match their title"] += 1
                return tag
            target = self.ctx.href(i, path)
            self.report["source links " + ("to Mathlib pages" if target else "left as written")] += 1
            return with_href(tag, target, "a") if target else tag

        def documentation(match: re.Match) -> str:
            tag = match.group()
            if attributes(tag).get("class") != "bp-lean-doc":
                return tag
            docs = DOCS_HREF.fullmatch(raw_href(tag))
            name = decoded(docs.group(1)) if docs else None
            i = graph.index.get(name) if name is not None else None
            if i is None or raw_href(tag) != esc(docs_href(graph.names[i])):
                return tag
            target = self.ctx.href(i, path)
            self.report["documentation links " + ("to Mathlib pages" if target else "left as written")] += 1
            return with_href(tag, target, "d") if target else tag

        page = A_TAG.sub(source, page) if MATHLIB_GIT + "/blob/" in page else page
        if "mathlib4_docs" not in page:
            return page
        return LEAN_BLOCK.sub(lambda block: A_TAG.sub(documentation, block.group()), page)

    def card(self, card: str, article: Article, path: str) -> str:
        graph = self.ctx.graph
        if article.status == "mathlib":
            meta = META_MATHLIB.search(card)
            i = graph.index.get(html.unescape(meta.group(2))) if meta else None
            if i is None:
                self.problems.append(f"{path}#{article.anchor}: the article's credited Mathlib declaration "
                                     f"{html.unescape(meta.group(2)) if meta else '(none)'} is not a Mathlib node")
            else:
                linked = f'<a href="{esc(self.ctx.link(i, path))}" data-ml="c">{meta.group(1)}</a>'
                card = card[: meta.start(1)] + linked + card[meta.end(1):]
                self.report["credited declarations linked"] += 1
        uses = article_uses(graph, article)
        if not uses[0] and not uses[1]:
            return card
        rows, total = [], 0
        for label, targets in (("Mathlib, statement", uses[0]), ("Mathlib, proof", uses[1])):
            listed = [t for t in targets if not graph.instance[t]]
            total += len(listed)
            if not listed:
                continue
            more = len(listed) - CARD_SHOWN
            # Autoform's status class for Mathlib gives each name the legend's "in mathlib" mark.
            text = " ".join(f'<a class="bp-ref bp-ref-mathlib" href="{esc(self.ctx.link(t, path))}">'
                            f"{esc(graph.names[t])}</a>" for t in listed[:CARD_SHOWN])
            text += f" and {more:,} more" if more > 0 else ""
            rows.append(f'<div class="bp-row ml-row"><span class="bp-key">{label}</span>'
                        f'<span class="bp-value">{text}</span></div>')
        if not rows:
            return card
        self.report["statement boxes listing Mathlib uses"] += 1
        details = DETAILS.search(card)
        if details:
            body = details.group(1)
            close, summary_end = body.rindex("</div>"), body.index("</summary>")
            body = (body[:summary_end] + f'<span class="ml-sum"> · Mathlib {total:,}</span>' + body[summary_end:close]
                    + "".join(rows) + body[close:])
            return card[: details.start(1)] + body + card[details.end(1):]
        close = card.rindex("</div>")
        return (card[:close] + f'<details class="bp-dependencies ml-added"><summary>Mathlib {total:,}</summary>'
                f'<div class="bp-dependency-body">{"".join(rows)}</div></details>' + card[close:])

    def cards(self, page: str, path: str) -> str:
        out, at = [], 0
        for start, end, node_id, anchor in boxes(page):
            article = canonical(self.ctx.site, path, node_id, anchor)
            out += [page[at:start], self.card(page[start:end], article, path) if article else page[start:end]]
            at = end
        return "".join(out) + page[at:]

    def home(self, page: str) -> str:
        at = page.find(HOME_ANCHOR)
        if at < 0:
            self.problems.append("index.html: no place for the link to the Mathlib pages")
            return page
        end = page.index("</div>", at) + len("</div>")
        entry = ('<div class="bp-hero-coverage ml-entry"><span class="bp-hero-coverage-counts">'
                 f"{count(len(self.ctx.hosted), 'Mathlib declaration')} by topic</span> "
                 '<span class="bp-hero-coverage-links">'
                 f'<a class="bp-hero-coverage-link" href="{SECTION}/index.html">Mathlib pages</a></span></div>')
        return page[:end] + entry + page[end:]

    def page(self, page: str, path: str) -> str:
        page = self.links(page, path)
        if "bp-thmwrapper" in page:
            page = self.cards(page, path)
        return self.home(page) if path == "index.html" else page


def scan_credits(site: Path, info: Site, graph: Graph) -> dict[int, list[Article]]:
    """Declarations that published articles credit: the article's status is `mathlib` in the catalog, and the name is
    the first Mathlib name of that same article's statement box."""
    credits: dict[int, list[Article]] = collections.defaultdict(list)
    for path in sorted({a.path for a in info.articles.values() if a.status == "mathlib"}):
        page = (site / path).read_text(encoding="utf-8")
        for start, end, node_id, anchor in boxes(page):
            article = canonical(info, path, node_id, anchor)
            meta = META_MATHLIB.search(page, start, end) if article and article.status == "mathlib" else None
            i = graph.index.get(html.unescape(meta.group(2))) if meta else None
            if i is not None:
                credits[i].append(article)
    return dict(credits)


def atlas_topic_pages(info: Site, plan: Plan) -> dict[tuple[str, str], tuple[str, str]]:
    """The ATLAS folder of each topic, when the roadmap has one: the topic's folder name, maybe numbered, with the
    topic's title."""
    found = {}
    for page in plan.pages:
        if page.topic is None or page.topic in found:
            continue
        to, title = page.topic
        base = f"{to}/{slugify(title)}"
        for candidate in [base, *(f"{base}-{n}" for n in range(2, 10))]:
            scope = info.scopes.get(candidate)
            if scope and scope[1].casefold() == title.casefold():
                found[page.topic] = scope
                break
    return found


# ---------------------------------------------------------------------------------------------------------------
# Moved index pages (docs/mathlib-pages.md#moved-index-pages)
#
# Module pages never move. Index pages do, when the taxonomy changes: the root, a scope's group page (a scope with a
# module) and a topic's page (a topic with at least two modules). The record of scripts/mathlib-moves.d, one fragment
# per change, says where some of them went; a notice stands at each recorded route that no page holds. A row is judged
# where it was introduced, against plans of commits recomputed on the run's graph, and never against today's taxonomy.
# What a run cannot read proves nothing: a row whose judgement needs it gets no authority.


MOVES = "scripts/mathlib-moves.d"
# The commit that added the Mathlib pages: no index page existed before it, so no row's commit precedes it.
PAGES_SINCE = "ec55a0d979f8dbcf57878526b29adf4f1870b827"
# How far back a shallow checkout fetches main's history, without blobs: a day before PAGES_SINCE, at midnight UTC, so
# that the clock's time of day does not move it.
HISTORY_SINCE = "2026-11-20T00:00:00Z"
# What the Mathlib graph is computed from, as the Mathlib layer job keys its cache: a commit's plan is recomputed on the
# run's graph only when these inputs are the run's. The `mathlib` entry of lake-manifest.json is compared as a value,
# these files byte for byte.
MANIFEST = "lake-manifest.json"
UNIVERSE_FILES = ("lean-toolchain", "scripts/dump_mathlib_dependencies.lean", "scripts/extract_mathlib_graph.py",
                  "scripts/extract_v2_lean_dependencies.py")
PLANNER = "scripts/build_mathlib_pages.py"
TAXONOMY_FILE = "scripts/taxonomy.json"
ROW_FIELDS = ("index", "existed_at", "kind", "title", "modules", "to")
SUBJECT_PART = re.compile(r"[A-Z][A-Za-z0-9]*")
FOLDER_PART = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
MODULE_NAME = re.compile(r"Mathlib(?:\.[^\s./]+)+")
FULL_COMMIT = re.compile(r"[0-9a-f]{40}")
TITLE_LIMIT = 200
# The rules of the card move ledger's fragment writer (scripts/card_moves.py) that this record's writer mirrors; a test
# holds them equal.
AHEAD = 3600
STAMP = "%Y%m%dT%H%M%SZ"
SLUG = re.compile(r"[a-z0-9][a-z0-9-]*")
# Git's modes of a regular file.
REGULAR = ("100644", "100755")
# Every notice holds this element, and no page does.
NOTICE = '<div class="ml-moved"'
# The record the build and the check read: this checkout's. Tests point it at a checkout of their own.
RECORD_ROOT = ROOT
# How long one git command may take: a fetch that hangs leaves the record unjudged, never the site unbuilt.
GIT_TIMEOUT = 600
# The exit statuses of check-moves (and of check, on a pull request): a verification of record that passes, a refusal
# or a run that certifies nothing, a usage error, the result of a module list, which is advisory whatever its rows
# give, and a record that cannot be established here, which is neither a pass nor a refusal.
CERTIFIED, REFUSED, USAGE, ADVISORY, UNRESOLVED = 0, 1, 2, 3, 4
# How check reports what leaves a pull request's record unresolved: such lines alone give UNRESOLVED.
NOT_CERTIFIED = "not certified: "


@dataclass
class RecordTree:
    """The record's folder as one commit or the working tree has it: its fragments, by path in the repository, in
    byte order of name; why each other entry is no fragment, by path (MOVES itself when it is no folder); and the
    identity of every entry, whatever it holds, as Git's mode, type and object id, by path: what a change must leave
    as it is."""

    files: list[tuple[str, bytes]] = field(default_factory=list)
    problems: dict[str, str] = field(default_factory=dict)
    entries: dict[str, tuple[str, str, str]] = field(default_factory=dict)

    def messages(self) -> list[str]:
        """What is wrong with the folder, as card_moves.read_fragments says it."""
        if MOVES in self.problems:
            return [f"{MOVES} {self.problems[MOVES]}"]
        return [f"{path}: {problem}" for path, problem in sorted(self.problems.items(),
                                                                key=lambda item: os.fsencode(item[0]))]


def occupant(mode: str, kind: str) -> str:
    """What an entry of the record's folder is, in words."""
    if kind == "tree":
        return "a folder"
    if kind == "commit":
        return "a submodule"
    return "a link" if mode == "120000" else "a file"


def object_format(repo: Path) -> str:
    """The object format of the repository ``repo``, `sha1` or `sha256`; `sha1` when it cannot be told."""
    found = git_run(repo, "rev-parse", "--show-object-format").stdout.decode().strip()
    return found if found in ("sha1", "sha256") else "sha1"


def tree_id(path: Path, form: str) -> str:
    """Git's id of the tree of the folder ``path``, as `git add` would record it."""
    entries = []
    for name in os.listdir(path):
        mode, kind, oid = fs_identity(path / name, form)
        if kind == "other":
            continue
        raw = os.fsencode(name)
        entries.append((raw + b"/" if kind == "tree" else raw, mode.lstrip("0").encode(), raw, oid))
    body = b"".join(mode + b" " + raw + b"\0" + bytes.fromhex(oid) for _, mode, raw, oid in sorted(entries))
    return hashlib.new(form, b"tree %d\0" % len(body) + body).hexdigest()


def fs_identity(path: Path, form: str) -> tuple[str, str, str]:
    """The identity Git gives the entry ``path`` of the working tree: its mode, type and object id. A folder holding
    a `.git` is a checked-out submodule, whose identity is its commit, as Git records it."""
    found = os.lstat(path)
    if stat.S_ISLNK(found.st_mode):
        return "120000", "blob", blob_id(os.fsencode(os.readlink(path)), form)
    if stat.S_ISREG(found.st_mode):
        return ("100755" if found.st_mode & stat.S_IXUSR else "100644"), "blob", blob_id(path.read_bytes(), form)
    if stat.S_ISDIR(found.st_mode):
        if os.path.lexists(path / ".git"):
            head = git_run(path, "rev-parse", "--verify", "--quiet", "HEAD")
            return "160000", "commit", head.stdout.decode().strip() if head.returncode == 0 else ""
        return "040000", "tree", tree_id(path, form)
    return "", "other", ""


def index_tree_id(leaves: list[tuple[str, str, str]], form: str) -> str:
    """Git's id of the tree that index entries ``leaves`` (each its path below the tree, mode and object id) make."""
    direct: list[tuple[bytes, bytes, str]] = []
    below: dict[str, list[tuple[str, str, str]]] = collections.defaultdict(list)
    for path, mode, oid in leaves:
        name, _, rest = path.partition("/")
        if rest:
            below[name].append((rest, mode, oid))
        else:
            direct.append((os.fsencode(name), mode.encode(), oid))
    direct += [(os.fsencode(name), b"40000", index_tree_id(sub, form)) for name, sub in below.items()]
    direct.sort(key=lambda entry: entry[0] + (b"/" if entry[1] == b"40000" else b""))
    body = b"".join(mode + b" " + raw + b"\0" + bytes.fromhex(oid) for raw, mode, oid in direct)
    return hashlib.new(form, b"tree %d\0" % len(body) + body).hexdigest()


def index_view(repo: Path, form: str) -> tuple[dict[str, tuple[str, str, str]], set[str]] | None:
    """What the index of the work tree ``repo`` holds of the record's folder: the identity of each entry in it (a
    folder's from the entries below it), or of the folder itself when it is a file, by path; and the entries the work
    tree has otherwise than the index (changed, removed, conflicted, untracked or ignored). Git, which reads a
    submodule it has not checked out as unchanged, says which. None when ``repo`` is no Git work tree's top or its
    index cannot be read."""
    prefix = git_run(repo, "rev-parse", "--show-prefix")
    if prefix.returncode != 0 or prefix.stdout.strip():
        return None
    staged = git_run(repo, "ls-files", "--stage", "-z", "--", MOVES)
    status = git_run(repo, "--no-optional-locks", "status", "--porcelain=v1", "-z", "--no-renames",
                     "--untracked-files=all", "--ignored=matching", "--", MOVES)
    if staged.returncode != 0 or status.returncode != 0:
        return None

    def entry_of(path: str) -> str | None:
        if path == MOVES:
            return MOVES
        if path.startswith(f"{MOVES}/"):
            return f"{MOVES}/{path[len(MOVES) + 1:].split('/', 1)[0]}"
        return None

    identities: dict[str, tuple[str, str, str]] = {}
    folders: dict[str, list[tuple[str, str, str]]] = collections.defaultdict(list)
    differs: set[str] = set()
    for line in filter(None, staged.stdout.split(b"\0")):
        head, _, raw = line.partition(b"\t")
        mode, oid, number = head.decode().split()
        path = os.fsdecode(raw)
        entry = entry_of(path)
        if entry is None:
            continue
        if number != "0":
            differs.add(entry)
        if path == entry:
            identities[entry] = (mode, {"160000": "commit"}.get(mode, "blob"), oid)
        else:
            folders[entry].append((path[len(entry) + 1:], mode, oid))
    for entry, leaves in folders.items():
        identities.setdefault(entry, ("040000", "tree", index_tree_id(leaves, form)))
    for line in filter(None, status.stdout.split(b"\0")):
        code, path = line[:2].decode(errors="replace"), os.fsdecode(line[3:])
        entry = entry_of(path)
        if entry is not None and (code[1] != " " or code in ("??", "!!") or "U" in code):
            differs.add(entry)
    return identities, differs


def scan_move_folder(folder: Path, repo: Path | None = None) -> RecordTree:
    """``folder``, a scripts/mathlib-moves.d of the working tree, read as read_move_fragments reads it, with the
    identity of every entry in the object format of ``repo``: when ``folder`` is the record of the work tree
    ``repo``, an entry the work tree has as the index has it takes the index's identity (a submodule Git has not
    checked out is its commit, not an empty folder), and any other the work tree's."""
    try:
        found = os.lstat(folder)
    except FileNotFoundError:
        return RecordTree()
    form = object_format(repo if repo is not None else folder.parent)
    view = index_view(repo, form) if repo is not None and folder == repo / MOVES else None
    identities, differs = view if view is not None else ({}, set())

    def identity(path: str, where: Path) -> tuple[str, str, str]:
        if path in identities and path not in differs:
            return identities[path]
        return fs_identity(where, form)

    if not stat.S_ISDIR(found.st_mode):
        return RecordTree([], {MOVES: "is no folder"}, {MOVES: identity(MOVES, folder)})
    tree = RecordTree()
    for name in sorted(os.listdir(folder), key=os.fsencode):
        path = f"{MOVES}/{name}"
        tree.entries[path] = identity(path, folder / name)
        problem = name_problem(name)
        if problem is None and not stat.S_ISREG(os.lstat(folder / name).st_mode):
            problem = "no regular file"
        if problem is None:
            data = (folder / name).read_bytes()
            problem = content_problem(data)
        if problem is None:
            tree.files.append((path, data))
        else:
            tree.problems[path] = problem
    return tree


def read_move_fragments(folder: Path) -> tuple[list[tuple[str, bytes]], list[str]]:
    """The fragments in ``folder`` (a scripts/mathlib-moves.d), each read once, in byte order of name, by path in the
    repository, and what is wrong with the folder, as card_moves.read_fragments reads scripts/card-moves.d, with its
    rules for names and contents (a test holds the two to one result on one corpus): an entry that is no fragment is
    left out and named; a missing folder holds none."""
    tree = scan_move_folder(folder)
    return tree.files, tree.messages()


@dataclass(frozen=True)
class MoveRow:
    """A row of the record: an index route that moved (``index``, below mathlib/, "" for the root), a commit of main
    where it existed, its owner there (kind, title and sorted modules) and where it went, a route or a module whose
    page stands for it."""

    path: str
    number: int
    index: str
    existed_at: str
    kind: str
    title: str
    modules: tuple[str, ...]
    to: str

    @property
    def where(self) -> str:
        return f"{self.path}:{self.number}"


def route_problem(route: object) -> str | None:
    """Why ``route`` is no index route: "" or 1 to 4 components below mathlib/, the first a subject's name, each other
    a folder name as slugify writes one, maybe numbered; so never `outside`, `.`, `..` or an empty component."""
    if not isinstance(route, str):
        return "not a string"
    parts = route.split("/")
    if route and (len(parts) > 4 or not SUBJECT_PART.fullmatch(parts[0])
                  or not all(FOLDER_PART.fullmatch(part) for part in parts[1:])):
        return (f"{route!r} is no index route: \"\" or 1 to 4 components, the first [A-Z][A-Za-z0-9]*, the others "
                "[a-z0-9]+(-[a-z0-9]+)*")
    return None


def row_problem(row: object) -> str | None:
    """Why a line's JSON value is no row of the record."""
    if not isinstance(row, dict) or set(row) != set(ROW_FIELDS):
        return "expected an object with exactly the keys " + ", ".join(ROW_FIELDS)
    if problem := route_problem(row["index"]):
        return f"index: {problem}"
    if not isinstance(row["existed_at"], str) or not FULL_COMMIT.fullmatch(row["existed_at"]):
        return "existed_at: not a full commit, 40 lowercase hexadecimal digits"
    if row["kind"] not in ("topic", "group"):
        return 'kind: "topic" or "group"'
    if not isinstance(row["title"], str) or not row["title"] or len(row["title"]) > TITLE_LIMIT:
        return f"title: a string of 1 to {TITLE_LIMIT} characters"
    modules = row["modules"]
    if (not isinstance(modules, list) or not modules or modules != sorted(set(modules))
            or not all(isinstance(module, str) and MODULE_NAME.fullmatch(module) for module in modules)):
        return "modules: Mathlib module names, sorted, each once, at least one"
    if not (isinstance(row["to"], str) and MODULE_NAME.fullmatch(row["to"])) and route_problem(row["to"]):
        return f"to: neither a Mathlib module nor an index route ({route_problem(row['to'])})"
    return None


def parse_rows(files: list[tuple[str, bytes]]) -> tuple[list[MoveRow], list[str]]:
    """The rows of fragments, in order, each named by its file and line, and the lines that are no row."""
    rows: list[MoveRow] = []
    problems: list[str] = []
    for path, data in files:
        for number, line in enumerate(data.decode("utf-8").splitlines(), 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                problems.append(f"{path}:{number}: not JSON")
                continue
            if problem := row_problem(row):
                problems.append(f"{path}:{number}: {problem}")
                continue
            rows.append(MoveRow(path, number, row["index"], row["existed_at"], row["kind"], row["title"],
                                tuple(row["modules"]), row["to"]))
    return rows, problems


@dataclass(frozen=True)
class Owner:
    """What holds an index route in a plan: a topic's page, or a group's (the root's too), with its title and the
    modules below it, sorted."""

    kind: str
    title: str
    modules: tuple[str, ...]


def route_of(path: str) -> str:
    """The route of an index page from its site path, mathlib/<route>/index.html; "" for mathlib/index.html."""
    return path[len(SECTION) + 1: -len("index.html")].rstrip("/")


def route_path(route: str) -> str:
    return f"{SECTION}/{route}/index.html" if route else f"{SECTION}/index.html"


def owners(plan) -> dict[str, Owner]:
    """The index routes of a plan, each with its owner. Any version's plan_pages makes such a plan: this reads only its
    pages' paths, kinds, titles, modules and children. The page of the modules outside the taxonomy has no route."""
    below = modules_below(plan)
    return {route_of(page.path): Owner("topic" if page.kind == "topic" else "group", page.title,
                                       tuple(sorted(below[page.path])))
            for page in plan.pages if page.kind in ("home", "group", "topic")}


def module_topics(modules: list[str], taxonomy: bytes) -> list[tuple[str, str] | None]:
    """Each module's topic in ``taxonomy``, as the Mathlib layer's join gives it (extract_mathlib_graph.py join): its
    own key's placement, else its nearest placed directory's; None when it is excluded or unplaced. A taxonomy the join
    refuses is a ValueError."""
    import extract_mathlib_graph as layer

    with tempfile.TemporaryDirectory() as work:
        path = Path(work) / "taxonomy.json"
        path.write_bytes(taxonomy)
        try:
            placements = layer.load_placements([path])
        except SystemExit as error:
            raise ValueError(f"the join refuses the taxonomy: {error}") from None
    topics: list[tuple[str, str] | None] = []
    for module in modules:
        found = layer.resolve(layer.module_key(module), placements)
        topics.append((found[1]["to"], found[1]["title"]) if found and "to" in found[1] else None)
    return topics


PLANNERS: dict[str, ModuleType] = {}


def planner(source: bytes) -> ModuleType:
    """A version of this file, loaded once by its bytes; this module itself for its own bytes. Only versions from
    commits of main, whose code was reviewed, and the checkout's own are loaded: a row's commit is read only once it is
    found on main's first-parent chain."""
    key = hashlib.sha256(source).hexdigest()
    if key not in PLANNERS:
        if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == key:
            PLANNERS[key] = sys.modules[__name__]
        else:
            # Registered before it runs: its dataclasses look their module up by name.
            name = f"_mathlib_planner_{key[:16]}"
            with tempfile.TemporaryDirectory() as work:
                file = Path(work) / "build_mathlib_pages.py"
                file.write_bytes(source)
                spec = importlib.util.spec_from_file_location(name, file)
                module = importlib.util.module_from_spec(spec)
                sys.modules[name] = module
                try:
                    spec.loader.exec_module(module)
                except BaseException:
                    del sys.modules[name]
                    raise
            PLANNERS[key] = module
    return PLANNERS[key]


def plan_index(source: bytes, taxonomy: bytes, modules: list[str], reserved: Collection[str]) -> dict[str, Owner]:
    """The index routes of the plan that the version ``source`` of this file makes of ``taxonomy`` and the modules
    ``modules``, one node each, joined to the taxonomy as the layer joins it, with the recorded routes ``reserved`` (a
    version older than the record takes none, and had none to take); a plan that cannot be made is a ValueError."""
    try:
        version = planner(source)
        tree = json.loads(taxonomy)
        graph = SimpleNamespace(names=modules, module=modules, name_line=[0] * len(modules),
                                topic=module_topics(modules, taxonomy))
        hosted = set(range(len(modules)))
        if "reserved" in inspect.signature(version.plan_pages).parameters:
            plan = version.plan_pages(graph, hosted, tree, reserved=frozenset(reserved))
        else:
            plan = version.plan_pages(graph, hosted, tree)
        return owners(plan)
    except (Exception, SystemExit) as error:
        raise ValueError(f"no plan: {error}") from None


class Unavailable(Exception):
    """What a run cannot read: a commit, a tree, a blob or main's history. It proves nothing about a row."""


UNIVERSE_NAMES = ("the mathlib entry of lake-manifest.json", *UNIVERSE_FILES)


def universe(read) -> tuple | None:
    """The universe inputs ``read`` gives (a path in the repository to its bytes, None when absent; it may raise
    Unavailable): the `mathlib` entry of lake-manifest.json, then the digest of each of UNIVERSE_FILES. None when any of
    them is absent or unreadable: such a universe is unknown, and equal to no other."""
    data = read(MANIFEST)
    if data is None:
        return None
    try:
        entry = next(package for package in json.loads(data)["packages"] if package.get("name") == "mathlib")
    except (ValueError, KeyError, TypeError, AttributeError, StopIteration):
        return None
    digests = []
    for path in UNIVERSE_FILES:
        data = read(path)
        if data is None:
            return None
        digests.append(hashlib.sha256(data).hexdigest())
    return (json.dumps(entry, sort_keys=True), *digests)


def differences(one: tuple, two: tuple) -> str:
    """The inputs in which two known universes differ."""
    return ", ".join(name for name, a, b in zip(UNIVERSE_NAMES, one, two) if a != b)


def universe_pin(found: tuple) -> str | None:
    """The Mathlib revision a known universe pins."""
    rev = json.loads(found[0]).get("rev")
    return rev if isinstance(rev, str) else None


def git_run(repo: Path, *arguments: str, timeout: int = GIT_TIMEOUT) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", "-C", str(repo), *arguments], capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        return subprocess.CompletedProcess(arguments, 1, b"", str(error).encode())


def blob_id(data: bytes, form: str = "sha1") -> str:
    """Git's id of a blob of ``data``, in the object format ``form``."""
    return hashlib.new(form, b"blob %d\0" % len(data) + data).hexdigest()


class History:
    """main's first-parent chain from ``tip`` back to PAGES_SINCE (``since``), and the files of its commits, read from
    the repository ``repo``. A shallow checkout, as CI's is, fetches what it lacks from `origin`, which needs no token:
    a commit by its id, then the chain since HISTORY_SINCE without blobs, which holds every commit a row may name, Git
    fetching a blob it lacks when it is read; a complete checkout fetches nothing. ``problem`` says why there is no
    tip, and ``chain_problem()`` why there is no chain. What cannot be read raises Unavailable, never an empty result:
    a path is absent only from a tree that was read."""

    def __init__(self, repo: Path, tip: str, since: str | None = None):
        self.repo, self.since = repo, since or PAGES_SINCE
        self.shallow = git_run(repo, "rev-parse", "--is-shallow-repository").stdout.strip() == b"true"
        self.problem: str | None = None
        self.tip = self.commit(tip)
        if self.tip is None:
            self.problem = f"{tip} is no commit Git can read here"
        self.chain: list[str] = []
        self.position: dict[str, int] = {}
        self._chain_problem: str | None = None
        self._walked = False

    def commit(self, revision: str) -> str | None:
        """The full id of ``revision``; a full id a shallow checkout lacks is fetched, without blobs."""
        for attempt in (0, 1):
            found = git_run(self.repo, "rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}")
            if found.returncode == 0:
                return found.stdout.decode().strip()
            if attempt or not FULL_COMMIT.fullmatch(revision) or not self.shallow:
                return None
            git_run(self.repo, "fetch", "--quiet", "--no-tags", "--depth=1", "--filter=blob:none", "origin", revision)
        return None

    def walk(self) -> None:
        if self._walked or self.tip is None:
            return
        self._walked = True
        for attempt in (0, 1):
            listing = git_run(self.repo, "rev-list", "--first-parent", self.tip, "--").stdout.decode().split()
            if self.since in listing:
                self.chain = listing[: listing.index(self.since) + 1][::-1]
                self.position = {commit: n for n, commit in enumerate(self.chain)}
                return
            if attempt or not self.shallow:
                break
            git_run(self.repo, "fetch", "--quiet", "--no-tags", "--filter=blob:none",
                    f"--shallow-since={HISTORY_SINCE}", "origin", self.tip)
        self._chain_problem = (f"{self.since[:12]}, where the Mathlib pages start, is not on the first-parent chain of "
                               f"{self.tip[:12]} as this checkout has it")

    def chain_problem(self) -> str | None:
        self.walk()
        return self.problem or self._chain_problem

    def at(self, commit: str) -> int | None:
        """The position of ``commit`` on the chain, 0 for PAGES_SINCE; None off it."""
        self.walk()
        return self.position.get(commit)

    def entries(self, treeish: str, *paths: str) -> list[tuple[str, str, str, str]]:
        """What `git ls-tree` lists: mode, type, object id and name; nothing for an absent path."""
        listing = git_run(self.repo, "ls-tree", "-z", treeish, "--", *paths)
        if listing.returncode != 0:
            raise Unavailable(f"the tree of {treeish[:12]} cannot be read here")
        found = []
        for entry in filter(None, listing.stdout.split(b"\0")):
            head, _, name = entry.partition(b"\t")
            mode, kind, oid = head.decode().split()
            found.append((mode, kind, oid, os.fsdecode(name)))
        return found

    def blob(self, oid: str, what: str) -> bytes:
        found = git_run(self.repo, "cat-file", "blob", oid)
        if found.returncode != 0:
            raise Unavailable(f"{what} cannot be read here")
        return found.stdout

    def read(self, commit: str, path: str) -> bytes | None:
        """The bytes of the file ``path`` at ``commit``; None when it is no regular file there."""
        found = [entry for entry in self.entries(commit, path) if entry[3] == path]
        if not found or found[0][1] != "blob" or found[0][0] not in REGULAR:
            return None
        return self.blob(found[0][2], f"{path} at {commit[:12]}")

    @functools.cached_property
    def form(self) -> str:
        """The repository's object format."""
        return object_format(self.repo)

    def inventory(self, commit: str) -> dict[str, tuple[str, str, str]]:
        """The identity (mode, type and object id) of every entry of the record's folder at ``commit``, whatever it
        holds, by path; of the folder itself when it is no folder."""
        for mode, kind, oid, path in self.entries(commit, MOVES):
            if path == MOVES:
                if kind != "tree":
                    return {MOVES: (mode, kind, oid)}
                return {f"{MOVES}/{name}": (mode_in, kind_in, oid_in)
                        for mode_in, kind_in, oid_in, name in self.entries(oid)}
        return {}

    def scan(self, commit: str) -> RecordTree:
        """The record's folder at ``commit``, read as scan_move_folder reads one of the working tree, from Git's
        trees."""
        entries = self.inventory(commit)
        if MOVES in entries:
            return RecordTree([], {MOVES: "is no folder"}, entries)
        tree = RecordTree(entries=entries)
        for path in sorted(entries, key=os.fsencode):
            mode, kind, oid = entries[path]
            problem = name_problem(path.rsplit("/", 1)[1])
            if problem is None and not (kind == "blob" and mode in REGULAR):
                problem = "no regular file"
            data = self.blob(oid, f"{path} at {commit[:12]}") if problem is None else b""
            problem = problem or content_problem(data)
            if problem is None:
                tree.files.append((path, data))
            else:
                tree.problems[path] = problem
        return tree

    def fragments(self, commit: str) -> tuple[list[tuple[str, bytes]], list[str]]:
        """The record's fragments at ``commit`` and what is wrong with its folder, as read_move_fragments reads a
        folder, from Git's trees."""
        tree = self.scan(commit)
        return tree.files, tree.messages()

    def introductions(self) -> dict[str, tuple[str, tuple[str, str, str]]]:
        """Where each path of the record's folder is first occupied on the chain, from PAGES_SINCE to the tip, by any
        kind of entry (a file, a folder, a link, a submodule), and by what: that commit, and the entry's mode, type and
        object id. A path is occupied from its first entry on, whatever came after, and a folder seen only through a
        path below it is a folder there. Every mode reads paths this one way."""
        if self.chain_problem():
            raise Unavailable(self.chain_problem())
        first: dict[str, tuple[int, str, tuple[str, str, str]]] = {}

        def occupy(path: str, commit: str, identity: tuple[str, str, str]) -> None:
            position = self.position[commit]
            known = first.get(path)
            if known is None or position < known[0] or (position == known[0] and not known[2][2]):
                first[path] = (position, commit, identity)

        for path, identity in self.inventory(self.since).items():
            if path != MOVES:
                occupy(path, self.since, identity)
        listing = git_run(self.repo, "log", "--first-parent", "--diff-merges=first-parent", "-r", "-t", "--raw",
                          "--no-renames", "--no-abbrev", "-z", "--format=commit %H", f"{self.since}..{self.tip}",
                          "--", MOVES)
        if listing.returncode != 0:
            raise Unavailable(f"main's history from {self.since[:12]} to {self.tip[:12]} cannot be read here")
        tokens = iter(listing.stdout.split(b"\0"))
        commit = ""
        for token in tokens:
            token = token.lstrip(b"\n")
            if token.startswith(b"commit "):
                commit = token[len(b"commit "):].decode()
            elif token.startswith(b":"):
                path = os.fsdecode(next(tokens, b""))
                fields = token[1:].decode().split()
                if len(fields) < 5 or commit not in self.position or not path.startswith(f"{MOVES}/"):
                    continue
                mode, oid = fields[1], fields[3]
                if set(mode) == {"0"}:
                    continue  # gone there: what was there came earlier
                name, _, below = path[len(MOVES) + 1:].partition("/")
                if below:
                    occupy(f"{MOVES}/{name}", commit, ("040000", "tree", ""))
                else:
                    occupy(path, commit, (mode, {"040000": "tree", "160000": "commit"}.get(mode, "blob"), oid))
        return {path: (commit, identity) for path, (_, commit, identity) in first.items()}

    def is_ancestor(self, ancestor: str, descendant: str) -> bool | None:
        """Whether ``ancestor`` is an ancestor of ``descendant``, or itself; None when that cannot be read."""
        found = git_run(self.repo, "merge-base", "--is-ancestor", ancestor, descendant)
        return {0: True, 1: False}.get(found.returncode)


@dataclass
class Snapshot:
    """What a plan is made from at a commit, or in the checkout's working tree: the version of this file, the taxonomy
    and the universe inputs; and why it cannot be read, if it cannot."""

    label: str
    commit: str | None
    planner: bytes | None
    taxonomy: bytes | None
    universe: tuple | None
    problem: str | None = None


@dataclass
class Verdict:
    """How a run takes a row: honoured or refused; where it was judged and how (its plans recomputed, or taken as
    stored after a proved change of universe inputs); whether its target shared no module with it there; whether it
    is a second honoured row for one topic route, which makes that route's notice plain; whether it is new (a pull
    request's); where its fragment was introduced on main; why; and whether its judgement could not be established,
    which is neither a pass nor a refusal."""

    row: MoveRow
    honoured: bool = False
    judged_at: str = ""
    how: str = ""
    plain: bool = False
    duplicate: bool = False
    new: bool = False
    position: int | None = None
    reason: str = ""
    unresolved: bool = False

    @property
    def state(self) -> str:
        return "honoured" if self.honoured else "unresolved" if self.unresolved else "refused"


@dataclass(frozen=True)
class Notice:
    """The notice at a recorded route that no page holds: whether it redirects, the live page it leads to, by site path,
    that page's title, and why it is plain."""

    index: str
    kind: str
    automatic: bool
    target: str
    title: str
    reason: str = ""


class MoveRecord:
    """The record of ``checkout``'s scripts/mathlib-moves.d judged for one run, on the modules of the run's graph:

    - each fragment main has (at ``base``, else at HEAD) at its introducing commit, the first of main's first-parent
      chain that has it, as it was there, against the reservations of the fragments of that commit's parent: there a
      failure is a warning and the row is not honoured, so it reserves nothing;
    - each new fragment, one main does not have, at the head (``head``, a commit whose tree is read, else the working
      tree), against the reservations of main's: with ``strict``, as on a pull request or for check-moves, a failure is
      an error.

    Each row is judged on its own, against the plan of its commit and P0, the plan of its judging commit with the
    reservations accepted before its fragment; a refused row reserves nothing and makes no other row a duplicate. The
    run's universe is that of the graph's producer commit (``producer``, its Mathlib pin ``pin`` checked against that
    commit's manifest), else the head's. A row whose commit or judging commit has, provably, other universe inputs than
    the run's cannot be recomputed: a new one is refused, one of main's is honoured as stored. A row whose judgement
    needs what cannot be read gets no authority. ``errors`` fail the check; ``warnings`` fail nothing, and the record
    never fails the build."""

    def __init__(self, modules: Iterable[str], checkout: Path | None = None, base: str | None = None,
                 strict: bool = False, head: str | None = None, producer: str | None = None, pin: str | None = None):
        self.modules = sorted(set(modules))
        self.module_set = set(self.modules)
        self.checkout = RECORD_ROOT if checkout is None else checkout
        self.base, self.strict, self.producer, self.pin = base, strict, producer, pin
        self.verdicts: list[Verdict] = []
        self.errors: list[str] = []
        self.warnings: list[str] = []
        # What the judgement needs and cannot establish, as (whether it is main's record, why); and from where on main's
        # chain (-1: everywhere; inf: the new rows) rows are judged against reservations that are therefore unknown.
        self.unresolved: list[tuple[bool, str]] = []
        self.unknown: list[tuple[float, str]] = []
        # The new fragments, the ones main's record does not have; and whether that could be established.
        self.fresh: list[tuple[str, bytes]] = []
        self.fresh_known = False
        self.history: History | None = None
        self.plans: dict[tuple, dict[str, Owner] | str] = {}
        self.snapshots: dict[str, Snapshot] = {}
        self.universe: tuple | None = None
        self.universe_problem: str | None = None
        self.universe_inconsistent = False
        self.head = self.snapshot(head)
        # The head's record folder: its fragments, and every entry's identity, whatever it holds.
        self.head_tree = RecordTree()
        try:
            self.head_tree = (scan_move_folder(self.checkout / MOVES, self.checkout) if head is None
                              else self.main.scan(head))
        except (Unavailable, OSError) as error:
            self.unresolve(f"the record cannot be read: {error}", True, -1)
            return
        if self.head_tree.entries or base is not None:
            try:
                self.universe = self.run_universe()
                self.judge(self.head_tree.files, self.head_tree.messages())
            except Exception as error:  # noqa: BLE001  the record never fails the build; the check says why
                for verdict in self.verdicts:
                    verdict.honoured, verdict.unresolved = False, True
                    verdict.reason = f"the record cannot be judged: {error!r}"
                self.unresolve(f"the record cannot be judged: {error!r}", True, -1)

    @property
    def prior_unresolved(self) -> bool:
        """Whether something main's record holds could not be established."""
        return any(prior for prior, _ in self.unresolved)

    def complain(self, message: str) -> None:
        """A problem that is established: an error when strict, a warning otherwise."""
        (self.errors if self.strict else self.warnings).append(message)

    def unresolve(self, reason: str, prior: bool, position: float) -> None:
        """What cannot be established: it proves nothing, so it is never taken for absent. The rows judged at or after
        ``position`` on main's chain (-1 for all, inf for the new rows) are judged against reservations that are
        unknown, and get no authority."""
        self.unresolved.append((prior, reason))
        self.unknown.append((position, reason))
        self.warnings.append(f"unresolved: {reason}")

    def blocked(self, position: float) -> str | None:
        """Why rows judged at ``position`` depend on what is unresolved, if they do."""
        return next((reason for at, reason in self.unknown if at <= position), None)

    @property
    def main(self) -> History:
        """main's history: from ``base``, else from HEAD."""
        if self.history is None:
            self.history = History(self.checkout, self.base or "HEAD")
        return self.history

    # What the rows are judged against

    def snapshot(self, commit: str | None) -> Snapshot:
        key = commit or ""
        if key not in self.snapshots:
            if commit is None:
                def read(path: str) -> bytes | None:
                    file = self.checkout / path
                    return file.read_bytes() if file.is_file() else None
            else:
                def read(path: str) -> bytes | None:
                    return self.main.read(commit, path)
            label = commit or "the checkout"
            try:
                self.snapshots[key] = Snapshot(label, commit, read(PLANNER), read(TAXONOMY_FILE), universe(read))
            except (Unavailable, OSError) as error:
                self.snapshots[key] = Snapshot(label, commit, None, None, None, str(error))
        return self.snapshots[key]

    def run_universe(self) -> tuple | None:
        """The universe of the run's graph: its producer's, once that commit is read and its manifest pins the graph's
        Mathlib; the head's when no producer is given, as a module list is taken to be. None, with why, when it cannot
        be established."""
        if self.producer is None:
            if self.head.universe is None:
                self.universe_problem = f"the universe inputs of {self.head.label[:12]} cannot all be read"
            return self.head.universe
        commit = self.main.commit(self.producer) if FULL_COMMIT.fullmatch(self.producer) else None
        if commit is None:
            self.universe_problem = (f"the graph's producer commit {self.producer or '(none)'} cannot be read here: "
                                     "the graph's universe is unknown")
            return None
        found = self.snapshot(commit)
        if found.universe is None:
            self.universe_problem = (f"the universe inputs of the graph's producer {commit[:12]} cannot all be read: "
                                     "the graph's universe is unknown")
            return None
        if self.pin is not None and universe_pin(found.universe) != self.pin:
            self.universe_problem = (f"the graph's Mathlib pin {self.pin or '(none)'} is not the one its producer "
                                     f"{commit[:12]} pins, {universe_pin(found.universe)}: the graph is inconsistent")
            self.universe_inconsistent = True
            return None
        return found.universe

    def plan(self, snapshot: Snapshot, reserved: Collection[str]) -> dict[str, Owner] | str:
        """The index routes of ``snapshot``'s plan with the recorded routes ``reserved``, or why there is none."""
        if snapshot.problem:
            return f"{snapshot.label[:12]}: {snapshot.problem}"
        if snapshot.planner is None or snapshot.taxonomy is None:
            return f"{snapshot.label[:12]} has no {PLANNER} or no {TAXONOMY_FILE}"
        key = (hashlib.sha256(snapshot.planner).hexdigest(), hashlib.sha256(snapshot.taxonomy).hexdigest(),
               tuple(sorted(reserved)))
        if key not in self.plans:
            try:
                self.plans[key] = plan_index(snapshot.planner, snapshot.taxonomy, self.modules, reserved)
            except ValueError as error:
                self.plans[key] = f"{snapshot.label[:12]}: {error}"
        return self.plans[key]

    @property
    def reserved_topics(self) -> frozenset[str]:
        """The topic routes the honoured rows hold: no topic takes them again."""
        return frozenset(v.row.index for v in self.verdicts if v.honoured and v.row.kind == "topic")

    @property
    def reserved(self) -> frozenset[str]:
        """The routes the honoured rows hold, topics' and groups' alike: no topic takes them (plan_pages)."""
        return frozenset(v.row.index for v in self.verdicts if v.honoured)

    def reserved_at(self, position: int | None) -> frozenset[str]:
        """The routes of the honoured rows of main's fragments introduced at or before ``position``."""
        return frozenset(v.row.index for v in self.verdicts if v.honoured and v.position is not None
                         and position is not None and v.position <= position)

    def at(self, commit: str) -> int | None:
        return self.history.at(commit) if self.history is not None else None

    # Judging

    def leave_unresolved(self, files: list[tuple[str, bytes]], reason: str, new: bool) -> None:
        """No authority, and no refusal either, for the rows of ``files``: what their judgement needs cannot be read."""
        rows, _ = parse_rows(files)
        self.verdicts += [Verdict(row, judged_at="nowhere", new=new, reason=reason, unresolved=True) for row in rows]

    def judge(self, files: list[tuple[str, bytes]], problems: list[str]) -> None:
        """The record's rows judged: main's fragments at their introduction, the first commit of main's chain that
        has their path, as its first entry was there; the head's new ones at the head. Every entry of main's record at
        the base stays as it is, by its identity (path, mode, type and object id), whatever it holds; a new fragment is
        a path main's record never had, by any kind of entry, at any point of its chain."""
        if self.universe is None:
            # A graph proved inconsistent is an error; one whose universe cannot be read leaves every row unresolved.
            why = f"{self.universe_problem or 'the run universe is unknown'}: no row can be recomputed"
            self.complain(why) if self.universe_inconsistent else self.unresolve(why, True, -1)
        history = self.main
        published: list[tuple[str, bytes]] | None = None
        if history.problem:
            unread = f"{history.problem}: main's record cannot be read"
        else:
            tip = history.tip
            try:
                published, broken = history.fragments(tip)
                before = history.inventory(tip)
            except Unavailable as error:
                published, unread = None, f"main's record at {tip[:12]} cannot be read: {error}"
        if published is None:
            # Which fragments are new, and whether a malformed entry is main's or new, cannot be told: never as if
            # main had none.
            for problem in problems:
                self.unresolve(f"{problem} (whether main's record has it cannot be told)", False, math.inf)
            self.unresolve(unread, True, -1)
            self.leave_unresolved(files, unread, self.strict)
            return
        after = self.head_tree.entries
        # Every entry main's record has stays as it is, by its identity, whatever it holds: one that holds no fragment
        # introduced no row there, and none can be introduced through it later.
        for path in sorted(before, key=os.fsencode):
            if path not in after:
                self.complain(f"{path}, an entry of main's record at {tip[:12]}, is gone; a published entry is never "
                              "deleted, renamed or made another kind of file, even one that holds no fragment")
            elif after[path] != before[path]:
                self.complain(f"{path}, an entry of main's record at {tip[:12]}, changed; a published entry is never "
                              "edited, even one that holds no fragment: put new rows in a new fragment")
        # A malformed entry main's record has, as it has it, is main's: a warning. One the change adds or changes is
        # the change's: an error.
        for path, problem in sorted(self.head_tree.problems.items(), key=lambda item: os.fsencode(item[0])):
            if before.get(path) != after.get(path):
                self.complain(f"{MOVES} {problem}" if path == MOVES else f"{path}: {problem}")
        for problem in broken:
            self.warnings.append(f"the record at {tip[:12]}: {problem}")
        # Which paths main's record has ever had, and the first entry of each: one rule for a pull request and for
        # main. What cannot be established leaves the rows unresolved, and which fragments are new unknown.
        candidates = [(path, data) for path, data in files if path not in before]
        try:
            occupied = history.introductions() if published or candidates else {}
        except Unavailable as error:
            self.unresolve(f"{error}: which paths main's record has had cannot be established", True, -1)
            self.leave_unresolved(published, str(error), False)
            self.leave_unresolved(candidates, str(error), self.strict)
            return
        # A new fragment is a path main's record never had, by any kind of entry, even one gone since.
        for path, data in candidates:
            if path in occupied:
                commit, (mode, kind, _) = occupied[path]
                self.complain(f"{path}: main's record had this path at {commit[:12]}, {occupant(mode, kind)}, so it is "
                              "no new fragment; a path main's record ever had is never used again, even once removed: "
                              "put new rows in a new fragment, under a new name")
            else:
                self.fresh.append((path, data))
        self.fresh_known = True
        now = datetime.now(timezone.utc)
        for path, _ in self.fresh:
            stamp = datetime.strptime(path.rsplit("/", 1)[1][:16], STAMP).replace(tzinfo=timezone.utc)
            if (stamp - now).total_seconds() > AHEAD:
                self.complain(f"{path} is stamped {stamp:%Y-%m-%d %H:%M:%S} UTC, ahead of this check's clock, "
                              f"{now:%Y-%m-%d %H:%M:%S} UTC; a stamp is the UTC time its fragment was made")
        # Main's fragments, each batch at the commit that first has its path, as its first entry was there, in the
        # chain's order: a path whose first entry is no fragment introduced no row, for good. One whose first entry
        # cannot be read is unresolved from there on, everywhere when that is unknown.
        batches: dict[str, list[tuple[str, bytes]]] = collections.defaultdict(list)
        for path, data in published:
            if path not in occupied:
                reason = f"{path}: no commit of main's first-parent chain has it, so its introduction cannot be judged"
                self.unresolve(reason, True, -1)
                self.leave_unresolved([(path, data)], reason, False)
                continue
            commit, (mode, kind, _) = occupied[path]
            problem = None if kind == "blob" and mode in REGULAR else f"no regular file: {occupant(mode, kind)}"
            then = b""
            if problem is None:
                try:
                    then = history.read(commit, path)
                except Unavailable as error:
                    self.unresolve(f"{path}: {error}", True, history.at(commit))
                    self.leave_unresolved([(path, data)], str(error), False)
                    continue
                problem = "no regular file" if then is None else content_problem(then)
            if problem is not None:
                self.warnings.append(f"{path} was introduced at {commit[:12]} as no fragment ({problem}): it "
                                     "introduced no row, and its later content is not honoured")
                continue
            if then != data:
                self.warnings.append(f"{path} changed after its introduction at {commit[:12]}: the rows introduced "
                                     "there are judged, and its later content is not honoured")
            batches[commit].append((path, then))
        for commit in sorted(batches, key=history.at):
            rows, bad = parse_rows(batches[commit])
            self.warnings += bad
            position = history.at(commit)
            self.judge_batch(rows, self.snapshot(commit), position - 1, False, position)
        rows, bad = parse_rows(self.fresh)
        for problem in bad:
            self.complain(problem)
        self.judge_batch(rows, self.head, history.at(tip), self.strict, None)

    def p0(self, judging: Snapshot, reserved: Collection[str]) -> tuple[dict[str, Owner] | None, tuple | None]:
        """P0, the plan of ``judging`` with the reservations ``reserved``; or why it cannot be made, as a state
        ("changed", why), a proved change of universe inputs, or ("unavailable", why)."""
        if judging.problem:
            return None, ("unavailable", f"{judging.label[:12]}: {judging.problem}")
        if judging.universe is not None and self.universe is not None and judging.universe != self.universe:
            return None, ("changed", f"the universe inputs of {judging.label[:12]} are not the run's "
                                     f"({differences(judging.universe, self.universe)})")
        if self.universe is None:
            return None, ("unavailable", self.universe_problem or "the run's universe is unknown")
        if judging.universe is None:
            return None, ("unavailable", f"the universe inputs of {judging.label[:12]} cannot all be read")
        found = self.plan(judging, reserved)
        return (None, ("unavailable", found)) if isinstance(found, str) else (found, None)

    def assess(self, row: MoveRow, at: int, p0: dict[str, Owner] | None, state: tuple | None,
               label: str) -> tuple[str, str, bool]:
        """Checks 2 to 5 of a row whose commit is on the chain, on its own: ("accepted", why, plain), ("refused", why,
        False), ("changed", why, False) when its commit or the judging commit provably has other universe inputs than
        the run's, or ("unavailable", why, False) when what its judgement needs cannot be read."""
        then = self.snapshot(row.existed_at)
        if then.universe is not None and self.universe is not None and then.universe != self.universe:
            return "changed", (f"the universe inputs of {row.existed_at[:12]} are not the run's "
                               f"({differences(then.universe, self.universe)})"), False
        if state is not None:
            return state[0], state[1], False
        if then.problem or then.universe is None:
            why = then.problem or f"the universe inputs of {row.existed_at[:12]} cannot all be read"
            return "unavailable", why, False
        witness = self.plan(then, self.reserved_at(at))
        if isinstance(witness, str):
            return "unavailable", witness, False
        route = row.index or "the root"
        owner = witness.get(row.index)
        if owner is None:
            return "refused", f"{route} is no index page in the plan of {row.existed_at[:12]}", False
        claimed = Owner(row.kind, row.title, row.modules)
        if owner != claimed:
            differ = [name for name in ("kind", "title", "modules") if getattr(owner, name) != getattr(claimed, name)]
            return "refused", (f"its {' and '.join(differ)} {'differs' if len(differ) == 1 else 'differ'} from its "
                               f"owner's in the plan of {row.existed_at[:12]}, the {owner.kind} {owner.title!r} with "
                               f"{count(len(owner.modules), 'module')}"), False
        if row.index in p0:
            held = p0[row.index]
            return "refused", f"{route} is live at {label[:12]}, the {held.kind} {held.title!r}: it did not move", False
        target = ((row.to,) if row.to in self.module_set else None) if MODULE_NAME.fullmatch(row.to) else (
            p0[row.to].modules if row.to in p0 else None)
        if target is None:
            return "refused", f"its target {row.to or 'the root'} is not live at {label[:12]}", False
        plain = not set(target) & set(row.modules)
        return "accepted", "its target shares no module with it: its notice is plain" if plain else "", plain

    def judge_batch(self, rows: list[MoveRow], judging: Snapshot, limit: int | None, strict: bool,
                    position: int | None) -> None:
        """The rows of the fragments one commit introduces, judged together at ``judging``: each row's commit is on
        main's chain at or before ``limit``, and each row passes on its own against its commit's plan and P0, the plan
        of ``judging`` with the reservations accepted before, none of these. Only the rows that pass are reserved, so
        that no two rows justify one another, and a second row for a topic route is a duplicate only of an accepted
        one: refused on a pull request, plain on main. A row whose judgement needs what cannot be read is unresolved,
        and so is every row judged after an unresolved one, whose reservations are unknown, unless what it fails does
        not depend on them: such rows are neither honoured nor refused."""
        if not rows:
            return
        p0, state = self.p0(judging, self.reserved)
        accepted = set(self.reserved_topics)
        # An established failure is an error for a new row only: main's rows that fail are warnings, and reserve
        # nothing (what is unresolved is kept apart, whichever rows it concerns).
        complain = self.errors.append if strict else self.warnings.append
        order = math.inf if position is None else position
        verdicts = []
        for row in rows:
            verdict = Verdict(row, judged_at=judging.label, new=strict, position=position)
            verdicts.append(verdict)
            at = self.at(row.existed_at)
            if at is None or limit is None or at > limit:
                verdict.reason = (f"existed_at {row.existed_at[:12]} is no commit of main's first-parent chain from "
                                  f"{PAGES_SINCE[:12]} to before {judging.label[:12]}")
                complain(f"{row.where}: {verdict.reason}")
                continue
            outcome, reason, plain = self.assess(row, at, p0, state, judging.label)
            blocker = self.blocked(order)
            if outcome == "changed" and strict:
                # Refused whatever the reservations are.
                verdict.reason = f"it cannot be recomputed ({reason}), and a new row must be"
                complain(f"{row.where}: {verdict.reason}")
                continue
            if outcome == "unavailable" or blocker is not None:
                verdict.unresolved = True
                if outcome == "unavailable":
                    verdict.reason = f"it cannot be verified ({reason}): unresolved"
                else:
                    known = ("on what is known it passes" if outcome in ("accepted", "changed") else
                             f"on what is known it is refused ({reason})")
                    verdict.reason = (f"unresolved, as the reservations it is judged against are unknown ({blocker}); "
                                      f"{known}")
                self.unresolve(f"{row.where}: {verdict.reason}", position is not None, order)
                continue
            duplicate = row.kind == "topic" and row.index in accepted
            if outcome in ("accepted", "changed"):
                if duplicate and strict:
                    verdict.reason = f"{row.index} has a row already, and a recorded topic route is reserved for good"
                    complain(f"{row.where}: {verdict.reason}")
                    continue
                verdict.honoured, verdict.plain, verdict.duplicate = True, plain, duplicate
                verdict.how = "recomputed" if outcome == "accepted" else "as stored"
                verdict.reason = reason if outcome == "accepted" else f"not recomputed: {reason}"
                if duplicate:
                    verdict.reason = (f"a second row for the topic route {row.index}: its notice is plain"
                                      + (f"; {verdict.reason}" if verdict.reason else ""))
                    self.warnings.append(f"{row.where}: {verdict.reason}")
                if row.kind == "topic":
                    accepted.add(row.index)
            else:
                verdict.reason = reason
                complain(f"{row.where}: {verdict.reason}")
        self.verdicts += verdicts

    # Notices

    def pick(self, route: str, rows: dict[str, list[MoveRow]]) -> tuple[MoveRow | None, str]:
        """The row that says where ``route`` went: its one topic row, or its group row whose commit comes latest on
        main's first-parent chain; or why there is none."""
        found = rows.get(route, [])
        name = route or "the root"
        if not found:
            return None, f"{name} is neither live nor recorded"
        if {row.kind for row in found} == {"topic"}:
            return (found[0], "") if len(found) == 1 else (None, f"{name} has {len(found)} honoured rows")
        if {row.kind for row in found} != {"group"}:
            return None, f"{name} has rows of both kinds"
        if len(found) == 1:
            return found[0], ""
        at = [self.at(row.existed_at) for row in found]
        if None in at:
            return None, f"{name} has several rows whose order on main is not known"
        if at.count(max(at)) > 1:
            return None, f"{name} has two rows at one commit, {found[at.index(max(at))].existed_at[:12]}"
        return found[at.index(max(at))], ""

    def notices(self, live: dict[str, Owner], hosted: Collection[str]) -> tuple[dict[str, Notice], list[str]]:
        """The notice of each honoured route that no page holds, ``live`` being the index routes of the site's plan and
        ``hosted`` the modules with a page, and what the resolution warns of. From the route's row, the targets are
        followed through their own honoured rows to a live page; the notice redirects there only when that page shares
        a module with what the route held. A repeated route, an ambiguous row, a target that cannot be verified or no
        live end gives a plain notice that leads to the nearest live index enclosing the last route reached."""
        rows: dict[str, list[MoveRow]] = collections.defaultdict(list)
        for verdict in self.verdicts:
            if verdict.honoured:
                rows[verdict.row.index].append(verdict.row)
        warnings: list[str] = []
        found: dict[str, Notice] = {}

        def fallback(route: str, kind: str, last: str, problem: str) -> None:
            parts = last.split("/") if last else []
            for end in range(len(parts) - 1, -1, -1):
                enclosing = "/".join(parts[:end])
                if enclosing in live:
                    warnings.append(f"{route}: {problem}; its notice is plain and leads to {enclosing or 'the root'}")
                    found[route] = Notice(route, kind, False, route_path(enclosing), live[enclosing].title, problem)
                    return
            warnings.append(f"{route}: {problem}, and no live index encloses it: it has no notice")

        for route in sorted(rows):
            if route in live:
                held = live[route]
                for row in rows[route]:
                    if (held.kind, held.title) != (row.kind, row.title):
                        warnings.append(f"{route or 'the root'} keeps the page of the {held.kind} {held.title!r}; "
                                        f"{row.where} records the {row.kind} {row.title!r}")
                continue
            chosen, problem = self.pick(route, rows)
            kind = (chosen or rows[route][0]).kind
            if chosen is None:
                fallback(route, kind, route, problem)
                continue
            seen, row, end = [route], chosen, None
            while end is None:
                if MODULE_NAME.fullmatch(row.to):
                    if row.to not in hosted:
                        problem = f"its target {row.to} has no page"
                        break
                    end = (module_path(row.to), row.to, (row.to,))
                elif row.to in live:
                    end = (route_path(row.to), live[row.to].title, live[row.to].modules)
                elif row.to in seen:
                    problem = f"its targets go round at {row.to or 'the root'}"
                    seen.append(row.to)
                    break
                else:
                    following, problem = self.pick(row.to, rows)
                    seen.append(row.to)
                    if following is None:
                        problem = f"its target {problem}"
                        break
                    row = following
            if end is None:
                fallback(route, kind, seen[-1], problem)
                continue
            automatic = bool(set(end[2]) & set(chosen.modules))
            found[route] = Notice(route, kind, automatic, end[0], end[1],
                                  "" if automatic else f"{end[0]} shares no module with what {route} held")
        return found, warnings

    # Reports

    @staticmethod
    def notice_label(route: str, notices: dict[str, Notice], live: Collection[str]) -> str:
        """What a route shows: the notice the build writes there, a page, or nothing; read from what is built, so that
        a receipt never says other than the site."""
        notice = notices.get(route)
        if notice is not None:
            return f"{'automatic' if notice.automatic else 'plain'}, to {notice.target}"
        return "none: a page holds the route" if route in live else "none"

    def receipt(self, notices: dict[str, Notice], warnings: list[str], live: Collection[str]) -> dict:
        """The honoured, refused and unresolved rows, with their reasons and what their routes show in the built site,
        what is unresolved, and the notices, for the build's report."""
        return {
            "rows": [{"row": v.row.where, "index": v.row.index, "to": v.row.to,
                      "verdict": v.state, "judged_at": v.judged_at, "how": v.how,
                      "duplicate": v.duplicate, "route_shows": self.notice_label(v.row.index, notices, live),
                      "reason": v.reason}
                     for v in self.verdicts],
            "notices": [{"index": n.index, "path": route_path(n.index),
                         "notice": "automatic" if n.automatic else "plain", "to": n.target, "reason": n.reason}
                        for _, n in sorted(notices.items())],
            "errors": list(self.errors),
            "unresolved": [f"{'prior record' if prior else 'new rows'}: {reason}" for prior, reason in self.unresolved],
            "warnings": self.warnings + warnings,
        }

    def advice(self, command: str) -> list[str]:
        """On a pull request whose base and head share universe inputs, what the two plans show that the record may
        lack; it never fails anything."""
        if self.history is None or self.history.problem or self.base is None:
            return []
        tip = self.history.tip
        base = self.snapshot(tip)
        if base.universe is None or self.head.universe is None or base.universe != self.head.universe:
            return [f"advice: {tip[:12]} and the head do not share known universe inputs: the plans are not compared"]
        before = self.plan(base, self.reserved_at(self.at(tip)))
        after = self.plan(self.head, self.reserved)
        if isinstance(before, str) or isinstance(after, str):
            return [f"advice: the plans are not compared: {before if isinstance(before, str) else after}"]
        recorded = {verdict.row.index for verdict in self.verdicts}
        lines = []
        for route in sorted(set(before) - set(after) - recorded):
            lines.append(f"advice: {route}, the {before[route].kind} {before[route].title!r}, vanishes without a row; "
                         f"`{command}` proposes rows")
        for route in sorted(set(before) & set(after)):
            one, two = before[route], after[route]
            shared = set(one.modules) & set(two.modules)
            if one.kind != two.kind or (one.kind == "topic" and (one.title != two.title or not shared)):
                lines.append(f"advice: {route or 'the root'} changes owner, from the {one.kind} {one.title!r} to the "
                             f"{two.kind} {two.title!r}" + ("" if shared else ", with no module in common"))
        natural: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
        for route, owner in after.items():
            if owner.kind == "topic":
                natural[(route.rsplit("/", 1)[0], slugify(owner.title))].append(route)
        for (scope, slug), routes in sorted(natural.items()):
            if len(routes) > 1:
                lines.append(f"advice: {len(routes)} topics of {scope} share the folder name {slug}: "
                             + ", ".join(sorted(routes)))
        scopes = set(taxonomy_tree(json.loads(self.head.taxonomy))[2])
        lines += [f"advice: the topic route {route} is a scope's path" for route, owner in sorted(after.items())
                  if owner.kind == "topic" and route in scopes]
        return lines


def propose(before: dict[str, Owner], after: dict[str, Owner], modules: Collection[str], existed_at: str,
            recorded: Collection[str] = ()) -> list[dict]:
    """A row for each index route of ``before`` that ``after`` lacks and no row records, ``existed_at`` being the commit
    of ``before``, its target traced by its modules: the index route or module page of ``after`` sharing most of them,
    the one with fewest modules among those, then one of the route's kind, then a route before a module page."""
    rows = []
    for route in sorted(set(before) - set(after) - set(recorded)):
        owner = before[route]
        held = set(owner.modules)
        candidates = [(-len(held & set(o.modules)), len(o.modules), o.kind != owner.kind, 0, r)
                      for r, o in after.items()]
        candidates += [(-1, 1, True, 1, module) for module in owner.modules if module in modules]
        best = min((c for c in candidates if c[0] < 0), default=None)
        if best is None:
            continue
        rows.append({"index": route, "existed_at": existed_at, "kind": owner.kind, "title": owner.title,
                     "modules": list(owner.modules), "to": best[4]})
    return rows


def site_name() -> str:
    """The site's name, mkdocs.yml's `site_name`, which ends every page's title."""
    try:
        found = re.search(r"^site_name:\s*(.+?)\s*$", (ROOT / "mkdocs.yml").read_text(encoding="utf-8"), re.M)
    except OSError:
        found = None
    return found.group(1).strip("\"'") if found else "ATLAS"


def notice_page(notice: Notice) -> str:
    """The notice at ``notice``'s route, in the form of the card pages' notices (hooks/card_pages.py, which
    hooks/trim_pages.py publishes as a bare document): a heading and a plain relative link to the live page; when
    automatic, a script that follows the link with `location.replace`, keeping the address's fragment when the link has
    none, a refresh for a reader without JavaScript and the link as canonical; never indexed by a search engine."""
    href = relative(notice.target, route_path(notice.index))
    noun = "section" if notice.kind == "group" else "page"
    heading = f"This {noun} moved" if notice.automatic else f"This {noun} was reorganised"
    head = ['<meta charset="utf-8">', '<meta name="viewport" content="width=device-width,initial-scale=1">',
            f"<title>{heading} - {esc(site_name())}</title>", '<meta name="robots" content="noindex">']
    body = [f"<h1>{heading}</h1>", f'{NOTICE} data-ml-notice="{"automatic" if notice.automatic else "plain"}">',
            f'<p><a href="{esc(href)}">Continue to {esc(notice.title)}</a></p>']
    if notice.automatic:
        head += [f'<link rel="canonical" href="{esc(href)}">',
                 f'<noscript><meta http-equiv="refresh" content="0; url={esc(href)}"></noscript>']
        target = json.dumps(href).replace("<", "\\u003c")
        body.append(f"<script>(function(){{var to=new URL({target},location.href);"
                    "if(!to.hash)to.hash=location.hash;location.replace(to.href)})();</script>")
    body.append("</div>")
    return ('<!doctype html>\n<html lang="en">\n<head>\n' + "\n".join(head) + "\n</head>\n<body>\n" + "\n".join(body)
            + "\n</body>\n</html>\n")


NOTICE_LINK = re.compile(r'<div class="ml-moved"[^>]*>\s*<p><a href="([^"]*)"')
NOTICE_CANONICAL = re.compile(r'<link rel="canonical" href="([^"]*)">')
NOTICE_REFRESH = re.compile(r'<meta http-equiv="refresh" content="0; url=([^"]*)">')
NOTICE_SCRIPT = re.compile(r'new URL(\("(?:[^"\\]|\\.)*"),location\.href\)')


def notice_problems(path: str, page: str) -> list[str]:
    """Whether a notice's link, canonical, refresh and script name one address: an automatic notice has all four, a
    plain one its link alone."""
    links = [html.unescape(x) for x in NOTICE_LINK.findall(page)]
    others = {"canonical": [html.unescape(x) for x in NOTICE_CANONICAL.findall(page)],
              "refresh": [html.unescape(x) for x in NOTICE_REFRESH.findall(page)],
              "script": [json.loads(x[1:]) for x in NOTICE_SCRIPT.findall(page)]}
    if len(links) != 1:
        return [f"{path}: a notice has one link, not {len(links)}"]
    automatic = 'data-ml-notice="automatic"' in page
    errors = []
    for role, found in others.items():
        if found != ([links[0]] if automatic else []):
            errors.append(f"{path}: its {role} is {found}, its link {links[0]}" if automatic else
                          f"{path}: a plain notice has no {role}")
    return errors


def pull_request_base() -> tuple[str | None, str | None]:
    """The base commit of the pull request a GitHub Actions run checks, from its event (GITHUB_EVENT_PATH), and what
    went wrong reading it; no base for any other run."""
    if os.environ.get("GITHUB_EVENT_NAME") != "pull_request":
        return None, None
    try:
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
        base = event["pull_request"]["base"]["sha"]
    except (KeyError, OSError, ValueError, TypeError) as error:
        return None, f"the pull request's base commit cannot be read from GITHUB_EVENT_PATH ({error!r})"
    if not isinstance(base, str) or not FULL_COMMIT.fullmatch(base):
        return None, f"the pull request's base commit is not a full commit: {base!r}"
    return base, None


def module_digest(modules: Iterable[str]) -> str:
    """The SHA-256 of a module inventory: its names, sorted, each once, one a line."""
    return hashlib.sha256("".join(f"{module}\n" for module in sorted(set(modules))).encode()).hexdigest()


@dataclass
class GraphInputs:
    """A mathlib-graph artifact as the record's commands read it, a directory or the ZIP CI serves: its versions, the
    modules of its nodes, and the digests that identify it, the ZIP's being the artifact's own digest."""

    source: str
    versions: dict
    modules: list[str]
    nodes_sha256: str
    stats_sha256: str
    zip_sha256: str | None

    @property
    def modules_sha256(self) -> str:
        return module_digest(self.modules)


GRAPH_FILES = ("stats.json", "nodes.jsonl.gz")


def zip_member(archive: zipfile.ZipFile, name: str) -> bytes:
    """The bytes of the one regular member of ``archive`` at ``name``. ZipFile.read takes the last of several members
    of one name, so a ZIP with no such member, or with several naming that path (``name``, ``./name``,
    ``dir/../name``, with either slash), is refused, as is a member that is a folder or a link: what it holds would be
    ambiguous or elsewhere."""
    found = [info for info in archive.infolist()
             if posixpath.normpath(info.filename.replace("\\", "/")) == name]
    if len(found) != 1:
        raise ValueError(f"the ZIP has {len(found)} members at {name}, not one: its inventory would be ambiguous")
    (info,) = found
    kind = stat.S_IFMT(info.external_attr >> 16)
    if info.filename != name or info.is_dir() or kind not in (0, stat.S_IFREG):
        raise ValueError(f"the ZIP's member {info.filename!r} is no regular file at {name}")
    return archive.read(info)


def read_graph_inputs(path: Path) -> GraphInputs:
    """A mathlib-graph artifact's stats.json and nodes.jsonl.gz, from a directory, where each is a regular file, or
    from its ZIP, where each is exactly one regular member (zip_member); an OSError, a KeyError, a ValueError or a
    zipfile.BadZipFile when it is none."""
    zip_digest = None
    if path.is_file():
        data = path.read_bytes()
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            stats, nodes = (zip_member(archive, name) for name in GRAPH_FILES)
        zip_digest = hashlib.sha256(data).hexdigest()
    else:
        for name in GRAPH_FILES:
            if not stat.S_ISREG(os.lstat(path / name).st_mode):
                raise ValueError(f"{path / name} is no regular file")
        stats, nodes = (path / "stats.json").read_bytes(), (path / "nodes.jsonl.gz").read_bytes()
    versions = json.loads(stats).get("versions") or {}
    modules: set[str] = set()
    with gzip.open(io.BytesIO(nodes), "rt", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                modules.add(json.loads(line)["module"])
    return GraphInputs(str(path), versions if isinstance(versions, dict) else {}, sorted(modules),
                       hashlib.sha256(nodes).hexdigest(), hashlib.sha256(stats).hexdigest(), zip_digest)


def fresh_moves_name(slug: str, known: dict[str, str], now: datetime) -> tuple[str, str | None]:
    """The name card_moves.py's new-moves would give a fragment of ``slug`` (fresh_name), here: the current UTC time
    or, if later, one second after the latest stamp of ``known`` (fragment names to where they are), so that it sorts
    after each of them; or "" and why none: after the last stamp a name can have, or more than AHEAD seconds past the
    clock, which the check refuses of a new fragment."""
    stamps = [(datetime.strptime(name[:16], STAMP).replace(tzinfo=timezone.utc), where)
              for name, where in known.items() if name_problem(name) is None]
    stamp = now.replace(microsecond=0)
    if stamps:
        latest, where = max(stamps)
        if latest == datetime.max.replace(microsecond=0, tzinfo=timezone.utc):
            return "", (f"{where} holds the last stamp a fragment's name can have, {latest:%Y-%m-%d %H:%M:%S} UTC: no "
                        "later four-digit stamp exists, so no fragment can sort after it, and waiting will not help; "
                        "rename or remove that fragment")
        stamp = max(stamp, latest + timedelta(seconds=1))
        if (stamp - now).total_seconds() > AHEAD:
            return "", (f"{where} is stamped {latest:%Y-%m-%d %H:%M:%S} UTC: a fragment sorting after it would be "
                        f"stamped more than an hour ahead of the clock, {now:%Y-%m-%d %H:%M:%S} UTC, which the check "
                        f"refuses of a new fragment; run again at {stamp - timedelta(seconds=AHEAD):%Y-%m-%d %H:%M:%S} "
                        "UTC or later")
    return f"{stamp:%Y%m%dT%H%M%SZ}-{slug}.jsonl", None


def write_moves(checkout: Path, slug: str, rows: list[dict], base: str, now: datetime | None = None) -> tuple[int, str]:
    """Write ``rows`` to a new fragment of ``checkout``'s scripts/mathlib-moves.d, named as card_moves.py's new-moves
    names one (fresh_moves_name), after every fragment of the folder and of the commit ``base``, which must be read in
    full; and what was done, or why not (status 1). scripts/ and the folder are real folders, opened without following
    a link, and the fragment is made exclusively: no file or link is written over or through."""
    now = datetime.now(timezone.utc) if now is None else now
    if not SLUG.fullmatch(slug):
        return 2, f"{slug!r} is no slug: [a-z0-9][a-z0-9-]*"
    if not rows:
        return 1, "no row to write: a fragment holds at least one"
    history = History(checkout, base)
    unreadable = (f"--base {base} is no commit Git can read here: a new name sorts after every fragment of the "
                  "checkout and of that commit, so it must be read")
    if history.problem:
        return 1, unreadable
    try:
        published, problems = history.fragments(history.tip)
    except Unavailable:
        return 1, unreadable
    if problems:
        return 1, (f"--base {base}: the commit's record cannot be read in full ({'; '.join(problems)}): a new name "
                   "sorts after every fragment of the checkout and of that commit, so it must be read")
    known = {path.rsplit("/", 1)[1]: f"{path} at {base}" for path, _ in published}
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    top = os.open(checkout, os.O_RDONLY | os.O_DIRECTORY)
    try:
        scripts = os.open("scripts", flags, dir_fd=top)
    except OSError:
        return 1, "scripts is no folder"
    finally:
        os.close(top)
    try:
        try:
            folder = os.open("mathlib-moves.d", flags, dir_fd=scripts)
        except FileNotFoundError:
            folder = None
        except OSError:
            return 1, f"{MOVES} is no folder"
        if folder is not None:
            known.update({name: f"{MOVES}/{name}" for name in os.listdir(folder)})
        name, problem = fresh_moves_name(slug, known, now)
        if problem:
            return 1, problem
        if folder is None:
            os.mkdir("mathlib-moves.d", dir_fd=scripts)
            folder = os.open("mathlib-moves.d", flags, dir_fd=scripts)
        try:
            try:
                descriptor = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644, dir_fd=folder)
            except FileExistsError:
                return 1, f"{MOVES}/{name} is there already; run again in a second"
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                handle.write("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
        finally:
            os.close(folder)
    finally:
        os.close(scripts)
    return 0, f"{MOVES}/{name}: {count(len(rows), 'row')}"


# ---------------------------------------------------------------------------------------------------------------
# build


def resolve_notices(moves: MoveRecord, plan: Plan) -> tuple[dict[str, Notice], list[str]]:
    """The notices of the record for the plan, and what the resolution warns of: none, with a warning, should the
    resolution fail, as the record never fails the build; the check resolves them the same way."""
    try:
        return moves.notices(owners(plan), set(plan.members))
    except Exception as error:  # noqa: BLE001
        return {}, [f"the notices cannot be resolved: {error!r}"]


def record_identity(moves: MoveRecord, graph: Graph) -> dict:
    """What the record was judged at and on: the head, the base, and the graph, this run's own artifact when its
    producer is the head."""
    head = git_run(moves.checkout, "rev-parse", "--verify", "--quiet", "HEAD^{commit}").stdout.decode().strip()
    return {"head": head or None, "base": moves.base,
            "graph": {"producer": graph.atlas_commit, "mathlib_rev": graph.rev,
                      "trust": "this run's own artifact" if head and head == graph.atlas_commit else "another commit's",
                      "modules": len(set(graph.module)), "modules_sha256": module_digest(graph.module)}}


def build(site: Path, graph_dir: Path, out: Path, mkdocs: list[str], keep: set[str] | None = None,
          record: Path | None = None, pull_request: str | None = None) -> dict:
    if out.exists():
        raise SystemExit(f"{out} exists")
    graph = load_graph(graph_dir)
    info = read_site(site)
    if info.commit != graph.atlas_commit:
        raise SystemExit(f"the site is ATLAS {info.commit or 'of an unknown revision'}, the Mathlib layer is ATLAS "
                         f"{graph.atlas_commit}")
    if any(path.startswith(f"{SECTION}/") for path in info.pages):
        raise SystemExit(f"the site already has a {SECTION}/ folder")
    if keep is None:
        hosted = set(range(len(graph.names)))
    else:
        unknown = sorted(keep - graph.index.keys())
        if unknown:
            raise SystemExit(f"{len(unknown)} declarations to keep are not Mathlib nodes, such as {unknown[:3]}")
        hosted = {graph.index[name] for name in keep}
    taxonomy = json.loads(TAXONOMY.read_text(encoding="utf-8"))
    _, descriptions, _, _ = taxonomy_tree(taxonomy)
    # The record of moved index pages (``record``'s scripts/mathlib-moves.d, this checkout's by default), judged on this
    # graph, as a pull request's check judges it when ``pull_request`` names its base: its honoured routes stay
    # reserved.
    moves = MoveRecord(graph.module, record, pull_request, strict=pull_request is not None,
                       producer=graph.atlas_commit, pin=graph.rev)
    plan = plan_pages(graph, hosted, taxonomy, reserved=moves.reserved)
    ctx = Context(graph, info, plan, hosted, scan_credits(site, info, graph), {})
    ctx.atlas_topics = atlas_topic_pages(info, plan)
    with tempfile.TemporaryDirectory() as work:
        chrome, search = render_chrome(plan, Path(work), mkdocs)
    shutil.copytree(site, out)
    docs = Docstrings(lambda name: ctx.href(graph.index[name]) if name in graph.index else None)
    below = modules_below(plan)
    for page in plan.pages:
        ctx.here = page.path
        body = render_module(ctx, page, docs) if page.kind == "module" else render_index(ctx, page, descriptions, below)
        target = out / page.path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(chrome[page.path].replace(SLOT, body), encoding="utf-8")
    (out / STYLESHEET_PATH).write_bytes(STYLESHEET.read_bytes())
    # A notice at each recorded route no page holds, out of the navigation, the search index and the counts.
    notices, notice_warnings = resolve_notices(moves, plan)
    for notice in notices.values():
        target = out / route_path(notice.index)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(notice_page(notice), encoding="utf-8")
    index = json.loads((out / SEARCH_INDEX).read_text(encoding="utf-8"))
    index["docs"].extend(search)
    (out / SEARCH_INDEX).write_text(
        json.dumps(index, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    enricher = Enricher(ctx)
    for path in info.pages:
        source = (site / path).read_text(encoding="utf-8")
        enriched = enricher.page(source, path)
        if enriched != source:
            (out / path).write_text(enriched, encoding="utf-8")
            enricher.report["ATLAS pages changed"] += 1
    return {
        "atlas_commit": graph.atlas_commit,
        "mathlib_rev": graph.rev,
        "declarations": len(hosted),
        "modules": len(plan.members),
        "mathlib_pages": len(plan.pages),
        "mathlib_notices": len(notices),
        "moves": {**moves.receipt(notices, notice_warnings, owners(plan)), **record_identity(moves, graph)},
        "credited_declarations": len(ctx.credits),
        "bridge_names_not_in_the_site": sum(1 for name in graph.bridge if name not in info.by_lean),
        "catalog_articles_not_published": info.unpublished,
        "links": dict(sorted(enricher.report.items())),
        "problems": enricher.problems,
    }


# ---------------------------------------------------------------------------------------------------------------
# check


RESTORE_BLOCKS = re.compile(
    r'<details class="bp-dependencies ml-added">.*?</details>'
    r'|<div class="bp-row ml-row">.*?</div>'
    r'|<span class="ml-sum">.*?</span>'
    r'|<div class="bp-hero-coverage ml-entry">.*?</div>',
    re.DOTALL,
)
CREDIT = re.compile(r'<a href="[^"]*" data-ml="c">(<code>[^<]*</code>)</a>')
MARKED = re.compile(r'<a\s[^>]*\sdata-ml="([ad])">')


def restore(page: str, path: str, graph: Graph) -> str:
    """The page `build` started from: its additions taken out and its links put back."""
    page = CREDIT.sub(r"\1", RESTORE_BLOCKS.sub("", page))

    def back(match: re.Match) -> str:
        tag, marker = match.group(), match.group(1)
        name = decoded(urlsplit(attributes(tag)["href"]).fragment)
        i = graph.index.get(name) if name is not None else None
        if i is None:
            raise ValueError(f"{path}: a link marked as a Mathlib page link names no Mathlib declaration")
        original = docs_href(graph.names[i]) if marker == "d" else graph.source(i)
        start = tag.index(' href="') + len(' href="')
        end = tag.index('"', start)
        suffix = f' data-ml="{marker}">'
        return f"{tag[:start]}{esc(original)}{tag[end:-len(suffix)]}>"

    return MARKED.sub(back, page)


def check(site: Path, graph_dir: Path, out: Path, record: Path | None = None, pull_request: str | None = None,
          advice: list[str] | None = None) -> list[str]:
    graph = load_graph(graph_dir)
    resolver = Resolver(out)
    expected = Expected(out, read_site(site), graph)
    errors: list[str] = []
    before = {p.relative_to(site).as_posix() for p in site.rglob("*") if p.is_file()}
    after = {p.relative_to(out).as_posix() for p in out.rglob("*") if p.is_file()}
    errors += [f"{path}: missing from the built site" for path in sorted(before - after)]
    errors += [f"{path}: added outside {SECTION}/" for path in sorted(after - before)
               if not path.startswith(f"{SECTION}/") and path != STYLESHEET_PATH]
    for path in sorted(before & after):
        old, new = (site / path).read_bytes(), (out / path).read_bytes()
        if old == new:
            continue
        if path == SEARCH_INDEX:
            a, b = json.loads(old), json.loads(new)
            extra = b["docs"][len(a["docs"]):]
            same = b["docs"][: len(a["docs"])] == a["docs"] and {**b, "docs": None} == {**a, "docs": None}
            if not same or any(not doc["location"].startswith(f"{SECTION}/") for doc in extra):
                errors.append(f"{path}: changed beyond the Mathlib pages' entries")
            errors += [f"{path}: {doc['location']} names no file" for doc in extra
                       if doc["location"] not in after]
            continue
        if not path.endswith(".html"):
            errors.append(f"{path}: changed")
            continue
        page = new.decode("utf-8")
        try:
            restored = restore(page, path, graph)
        except ValueError as error:
            errors.append(str(error))
            continue
        if restored.encode("utf-8") != old:
            text = old.decode("utf-8")
            at = next((n for n, (x, y) in enumerate(zip(text, restored)) if x != y), min(len(text), len(restored)))
            errors.append(f"{path}: changed beyond the Mathlib links and additions, at {at}: "
                          f"{restored[max(0, at - 80):at + 80]!r}")
        # Every link the build added or changed resolves, and exactly where the build would have put it.
        blocks = "".join(block.group() for block in RESTORE_BLOCKS.finditer(page))
        added = [m.group() for m in REFERENCE.finditer(blocks)]
        added += [m.group() for m in REFERENCE.finditer(page) if " data-ml=" in m.group()]
        errors += [error for tag in added if (error := resolver.check(path, tag))]
        for match in ROW_LINK.finditer(blocks):
            errors += expected.declaration(path, match.group(1), match.group(2))
        for match in CREDIT_LINK.finditer(page):
            errors += expected.declaration(path, match.group(1), match.group(2))
        for match in MARKED.finditer(page):
            attrs = attributes(match.group())
            if decoded(urlsplit(attrs["href"]).fragment) != attrs.get("title") or attrs["title"] not in expected.hosted:
                errors.append(f"{path}: the Mathlib page link titled {attrs.get('title')!r} leads to {attrs['href']}")
            else:
                errors += expected.declaration(path, esc(attrs["href"]), esc(attrs["title"]))
        if path == "index.html" and 'href="mathlib/index.html">' not in blocks:
            errors.append("index.html: the link to the Mathlib pages is not mathlib/index.html")
    for path in sorted(after - before):
        if path.endswith(".html"):
            page = (out / path).read_text(encoding="utf-8")
            errors += [error for m in REFERENCE.finditer(page) if (error := resolver.check(path, m.group()))]
            errors += expected.page(path, page)
    return errors + check_notices(out, graph, after - before, record, pull_request, advice)


def check_notices(out: Path, graph: Graph, added: set[str], record: Path | None, pull_request: str | None,
                  advice: list[str] | None) -> list[str]:
    """The notices both ways, from the record judged again: each honoured route that no page holds has its notice,
    exactly as its row gives it, no other file is a notice, and each notice's link, refresh, canonical and script name
    one address; no notice is in the search index. On a pull request (``pull_request``, its base), the graph is this
    run's own artifact, its producer the checkout's HEAD, the pull request's new rows must pass, and the record must be
    established: what is unresolved is reported on lines of its own (NOT_CERTIFIED); ``advice`` gets what the base's
    and the head's plans show."""
    moves = MoveRecord(graph.module, record, pull_request, strict=pull_request is not None,
                       producer=graph.atlas_commit, pin=graph.rev)
    errors = list(moves.errors)
    if pull_request is not None:
        # What cannot be established is neither a pass nor a refusal (main gives such lines alone UNRESOLVED).
        errors += [f"{NOT_CERTIFIED}{'prior record unresolved' if prior else 'unresolved'}: {reason}"
                   for prior, reason in moves.unresolved]
        head = git_run(moves.checkout, "rev-parse", "--verify", "--quiet", "HEAD^{commit}").stdout.decode().strip()
        if head != graph.atlas_commit:
            errors.append(f"the graph is of {graph.atlas_commit[:12]}, not of this checkout's HEAD {head[:12] or '?'}: "
                          "a pull request's rows are judged on its own run's graph")
    if advice is not None:
        advice += moves.advice(f"python scripts/build_mathlib_pages.py moves --base {pull_request} --graph GRAPH")
    expected: dict[str, str] = {}
    if any(verdict.honoured for verdict in moves.verdicts):
        # The plan of the build that wrote OUT: its pages depend on which modules have hosted declarations alone.
        hosted_modules = {module for module in set(graph.module) if (out / module_path(module)).is_file()}
        hosted = {i for i, module in enumerate(graph.module) if module in hosted_modules}
        plan = plan_pages(graph, hosted, json.loads(TAXONOMY.read_text(encoding="utf-8")), reserved=moves.reserved)
        notices, _ = resolve_notices(moves, plan)
        expected = {route_path(notice.index): notice_page(notice) for notice in notices.values()}
    found = set()
    for path in sorted(added):
        if path.startswith(f"{SECTION}/") and path.endswith(".html"):
            page = (out / path).read_text(encoding="utf-8")
            if NOTICE in page:
                found.add(path)
                if path not in expected:
                    errors.append(f"{path}: a notice that no honoured row of the record leaves there")
                errors += notice_problems(path, page)
    for path, page in sorted(expected.items()):
        if path not in added:
            errors.append(f"{path}: missing, the notice of its honoured row")
        elif (out / path).read_text(encoding="utf-8") != page:
            errors.append(f"{path}: not the notice its honoured row gives")
    if found and (out / SEARCH_INDEX).is_file():
        docs = json.loads((out / SEARCH_INDEX).read_text(encoding="utf-8")).get("docs", [])
        errors += [f"{SEARCH_INDEX}: {doc['location']} is a notice, which stays out of search" for doc in docs
                   if str(doc.get("location", "")).split("#")[0] in found]
    return errors


ROW_LINK = re.compile(r'<a class="bp-ref bp-ref-mathlib" href="([^"]*)">([^<]*)</a>')
CREDIT_LINK = re.compile(r'<a href="([^"]*)" data-ml="c"><code>([^<]*)</code></a>')
BLOCK = re.compile(r'<div class="ml-decl" id="([^"]*)">')
USES = re.compile(r'<p class="ml-(?:uses|used)">(.*?)</p>', re.DOTALL)
ATLAS_LINKS = re.compile(r'<p class="ml-(?:atlas|credit)">(.*?)</p>', re.DOTALL)
DOC_LINK = re.compile(r'<code><a href="([^"]*)">([^<]*)</a></code>')
LINK = re.compile(r'<a href="([^"]*)">([^<]*)</a>')


class Expected:
    """Where `build` links a declaration from a page, by the built site itself: to its block on its module's page
    when that page has it, else to its pinned source line; and where an ATLAS article is published."""

    def __init__(self, out: Path, site: Site, graph: Graph):
        self.graph = graph
        self.hosted: set[str] = set()
        for module in sorted(set(graph.module)):
            page = out / module_path(module)
            if page.is_file():
                found = {html.unescape(x) for x in BLOCK.findall(page.read_text(encoding="utf-8"))}
                self.hosted.update(n for n in found if n in graph.index and graph.module[graph.index[n]] == module)
        self.articles = {(a.path, a.anchor) for a in site.articles.values()}

    def link(self, name: str, here: str) -> str:
        i = self.graph.index[name]
        if name not in self.hosted:
            return self.graph.source(i)
        page, anchor = module_path(self.graph.module[i]), "#" + fragment(name)
        return anchor if page == here else relative(page, here) + anchor

    def declaration(self, here: str, raw: str, text: str) -> list[str]:
        """A link written `<a href="raw">text</a>` to the declaration named `text`."""
        name, href = html.unescape(text), html.unescape(raw)
        if name not in self.graph.index or href != self.link(name, here):
            return [f"{here}: the link to {name} leads to {href}"]
        return []

    def page(self, here: str, page: str) -> list[str]:
        """The links a Mathlib page writes to declarations and to ATLAS articles."""
        errors = []
        marks = list(BLOCK.finditer(page))
        for n, mark in enumerate(marks):
            block = page[mark.start(): marks[n + 1].start() if n + 1 < len(marks) else len(page)]
            name = html.unescape(mark.group(1))
            if name not in self.hosted or module_path(self.graph.module[self.graph.index[name]]) != here:
                errors.append(f"{here}: the block of {name} is not on its module's page")
            for uses in USES.finditer(block):
                for m in LINK.finditer(uses.group(1)):
                    errors += self.declaration(here, m.group(1), m.group(2))
            errors += [e for m in DOC_LINK.finditer(block) for e in self.declaration(here, m.group(1), m.group(2))]
            for paragraph in ATLAS_LINKS.finditer(block):
                for m in LINK.finditer(paragraph.group(1)):
                    target = urlsplit(html.unescape(m.group(1)))
                    route = (posixpath.normpath(posixpath.join(posixpath.dirname(here), target.path)), target.fragment)
                    if route not in self.articles:
                        errors.append(f"{here}: {m.group(1)} is not a published ATLAS article")
        return errors


REFERENCE = re.compile(r'<(?:a|link|script|img)\s[^>]*?(?:href|src)="[^"]*"[^>]*>')
REFERENCE_VALUE = re.compile(r'\s(?:href|src)="([^"]*)"')
IDS = re.compile(r'\sid="([^"]*)"')


class Resolver:
    """Whether a relative reference of a page of the built site names a file and, with a fragment, an id in it."""

    def __init__(self, out: Path):
        self.out = out
        self.ids: dict[str, set[str]] = {}
        self.exists: dict[str, bool] = {}

    def check(self, path: str, tag: str) -> str | None:
        href = html.unescape(REFERENCE_VALUE.search(tag).group(1))
        target = urlsplit(href)
        if target.scheme or target.netloc:
            return None
        file = posixpath.normpath(posixpath.join(posixpath.dirname(path), target.path)) if target.path else path
        if file not in self.exists:
            self.exists[file] = not file.startswith("../") and (self.out / file).is_file()
        if not self.exists[file]:
            return f"{path}: {href} names no file"
        if target.fragment and file.endswith(".html"):
            if file not in self.ids:
                self.ids[file] = {html.unescape(x) for x in IDS.findall((self.out / file).read_text(encoding="utf-8"))}
            if decoded(target.fragment) not in self.ids[file]:
                return f"{path}: {href} names no anchor"
        return None


# ---------------------------------------------------------------------------------------------------------------


def inventory(args: argparse.Namespace) -> tuple[list[str], str, GraphInputs | None]:
    """The run's modules for moves and check-moves: those of a mathlib-graph artifact, a directory or its ZIP, or of a
    list; a description of them; and the graph."""
    if args.graph is not None:
        graph = read_graph_inputs(args.graph)
        return graph.modules, (f"the {len(graph.modules):,} modules with a node of {args.graph} (Mathlib "
                               f"{graph.versions.get('mathlib_rev', '?')}, ATLAS "
                               f"{graph.versions.get('atlas_commit', '?')})"), graph
    modules = sorted({line.strip() for line in args.modules.read_text(encoding="utf-8").splitlines() if line.strip()})
    return modules, f"the {len(modules):,} modules listed in {args.modules}", None


def checkout_problem() -> str | None:
    """Why the writer would not write in the checkout it is run from: that checkout is the Git top level of the current
    folder, and the script run is its own scripts/build_mathlib_pages.py, as card_moves.py's helpers require."""
    invoked = Path(__file__).absolute()
    found = git_run(Path.cwd(), "rev-parse", "--show-toplevel")
    if found.returncode != 0:
        return "the writer writes in the checkout it is run from, and the current folder is in no Git checkout"
    top = Path(os.path.realpath(found.stdout.decode().strip()))
    if ((invoked.parent.name, invoked.name) != ("scripts", "build_mathlib_pages.py")
            or Path(os.path.realpath(invoked.parent.parent)) != top or Path(os.path.realpath(RECORD_ROOT)) != top):
        return f"{invoked} is not the scripts/build_mathlib_pages.py of the checkout it is run from, {top}"
    return None


def moves_command(args: argparse.Namespace) -> int:
    """Propose rows for the index routes that vanish between a commit and the checkout (--base), or across a commit of
    main (--at, from its first parent), on the run's modules; with --write, put them in a new fragment. Proposals are
    advisory: the rows are judged by check-moves and by the pull request's check."""
    modules, source, _ = inventory(args)
    record = MoveRecord(modules, base=args.base)
    for warning in record.errors + record.warnings:
        print(f"warning: {warning}", file=sys.stderr)
    history = record.main
    if history.problem:
        print(f"error: {history.problem}", file=sys.stderr)
        return 1
    if args.at is not None:
        commit, parent = history.commit(args.at), history.commit(f"{args.at}^1")
        if commit is None or parent is None or record.at(commit) is None:
            print(f"error: {args.at} is no commit of main's first-parent chain since {PAGES_SINCE[:12]} with a parent",
                  file=sys.stderr)
            return 1
        before = record.plan(record.snapshot(parent), record.reserved_at(record.at(parent)))
        after = record.plan(record.snapshot(commit), record.reserved_at(record.at(commit)))
        recorded = {v.row.index for v in record.verdicts if v.position is not None and v.position <= record.at(commit)}
    else:
        parent = history.tip
        before = record.plan(record.snapshot(parent), record.reserved_at(record.at(parent)))
        after = record.plan(record.head, record.reserved)
        recorded = {verdict.row.index for verdict in record.verdicts}
    for plan in (before, after):
        if isinstance(plan, str):
            print(f"error: {plan}", file=sys.stderr)
            return 1
    print(f"# Proposals (advisory): index routes of {parent[:12]} that {args.at[:12] if args.at else 'the checkout'} "
          f"lacks, on {source}", file=sys.stderr)
    rows = propose(before, after, record.module_set, parent, recorded)
    for row in rows:
        print(json.dumps(row, ensure_ascii=False))
    if args.write is None:
        return 0
    if problem := checkout_problem():
        print(f"error: {problem}", file=sys.stderr)
        return 1
    try:
        now = None if args.now is None else datetime.strptime(args.now, STAMP).replace(tzinfo=timezone.utc)
    except ValueError:
        print(f"error: --now {args.now} is no UTC time written YYYYMMDDTHHMMSSZ", file=sys.stderr)
        return 2
    status, message = write_moves(RECORD_ROOT, args.write, rows, args.base or "origin/main", now)
    print(message if status == 0 else f"error: {message}", file=sys.stderr if status else sys.stdout)
    return status


def check_moves_command(args: argparse.Namespace) -> int:
    """The pull request's check of its new rows, run by their author on the head commit, whose tree alone is read: the
    receipt a pull request that changes the record alone carries, as the workflow does not build it.

    With --graph, a verification of record: the graph is node-bearing, its producer commit is read and is the head or a
    commit of main's first-parent chain, its Mathlib pin is the one that commit's manifest pins, and its universe
    inputs are the head's; the base is a strict ancestor of the head, the head adds at least one row, and this script
    is the head's own. The receipt names the full head and base, the new fragments by blob and row count, and the
    graph by its digests and its sorted modules' count and digest, for reviewers to compare with the pull request and
    with the CI artifact. Main's rows are judged as on main: one that fails is a warning. Exit 0 when it certifies that
    every new row passes; 1 when a new row is refused, the change has another error, or something established makes
    certifying impossible; 4 when what the judgement needs cannot be established here (main's record or a row of it, a
    reservation, a witness, the base, which fragments are new), which is neither a pass nor a refusal. With --modules,
    the same judgement on a module list, which establishes no graph: advisory, exit 3."""
    found = git_run(RECORD_ROOT, "rev-parse", "--verify", "--quiet", "HEAD^{commit}")
    if found.returncode != 0:
        print("error: the checkout has no commit to judge", file=sys.stderr)
        return REFUSED
    head = found.stdout.decode().strip()
    try:
        modules, source, graph = inventory(args)
    except (OSError, KeyError, ValueError, zipfile.BadZipFile) as error:
        print(f"not certified: {args.graph or args.modules} cannot be read as a module inventory: {error}")
        print("result: not certified")
        return REFUSED
    advisory = graph is None
    producer = None if advisory else str(graph.versions.get("atlas_commit") or "")
    pin = None if advisory else str(graph.versions.get("mathlib_rev") or "")
    record = MoveRecord(modules, base=args.base, strict=True, head=head, producer=producer, pin=pin)
    history = record.main
    base = history.tip
    # What is established and refuses (exit 1), and what cannot be established here (exit 4, unless something
    # refuses): what cannot be read is never taken for what it would have shown.
    blocking: list[str] = []
    unknown: list[str] = []
    if history.problem:
        unknown.append(history.problem)
    elif base == head:
        blocking.append("the base is the head: a receipt certifies what a head adds to its base")
    else:
        ancestor = history.is_ancestor(base, head)
        if ancestor is None:
            unknown.append(f"whether the base {base[:12]} is an ancestor of the head cannot be read here")
        elif not ancestor:
            blocking.append(f"the base {base[:12]} is not an ancestor of the head: rebase on it, or give the merge "
                            "base")
    # The judgement is this script's, and the join and the fragments' rules are those of the scripts it imports.
    for path in (PLANNER, "scripts/card_moves.py", "scripts/extract_mathlib_graph.py",
                 "scripts/extract_v2_lean_dependencies.py"):
        try:
            theirs = record.main.read(head, path)
        except Unavailable as error:
            unknown.append(f"the head's {path} cannot be read here ({error})")
            continue
        try:
            ours = (Path(__file__).resolve().parent / Path(path).name).read_bytes()
        except OSError as error:
            unknown.append(f"the {path} run cannot be read here ({error})")
            continue
        if theirs != ours:
            blocking.append(f"the {path} run is not the head's: run the head's own scripts, unchanged")
    new = [verdict for verdict in record.verdicts if verdict.new]
    if not record.fresh_known:
        # Main's record could not be read: what the head adds is unknown, not nothing (the record says why).
        pass
    elif not record.fresh:
        blocking.append("the head adds no fragment to its base: there is nothing to certify")
    elif not new:
        blocking.append("the head's new fragments hold no row: there is nothing to certify")
    if not advisory:
        if not graph.modules:
            blocking.append("the graph has no node")
        if record.universe is None:
            blocking.append(record.universe_problem or "the graph's universe is unknown")
        else:
            made = history.commit(producer)
            if made != head and history.chain_problem():
                unknown.append(f"whether the graph's producer {producer[:12]} is on main's first-parent chain cannot "
                               f"be established ({history.chain_problem()})")
            elif made != head and history.at(made) is None:
                blocking.append(f"the graph's producer {producer[:12]} is neither the head nor a commit of main's "
                                f"first-parent chain from {PAGES_SINCE[:12]}")
            if record.head.problem:
                # Unreadable here is unknown, never a mismatch.
                unknown.append(f"the head's planner, taxonomy or universe inputs cannot all be read here "
                               f"({record.head.problem})")
            elif record.head.universe is None:
                blocking.append("the head lacks a universe input, or its manifest pins no Mathlib: its universe is "
                                "unknown")
            elif record.head.universe != record.universe:
                blocking.append(f"the graph's producer {producer[:12]} has other universe inputs than the head "
                                f"({differences(record.universe, record.head.universe)}): the graph cannot stand for "
                                "the head's plans")
    live = record.plan(record.head, record.reserved)
    live = live if isinstance(live, dict) else {}
    notices, _ = record.notices(live, record.module_set)
    print("check-moves receipt: "
          + ("ADVISORY, NOT A VERIFICATION OF RECORD" if advisory else "verification of record"))
    print(f"head: {head} (its commit tree is judged; the working tree is not read)")
    print(f"base: {base or args.base}")
    if advisory:
        print(f"modules: {source}, sorted list sha256 {module_digest(modules)}: a list establishes no graph")
    else:
        made = history.commit(producer) if producer else None
        where = ("the head" if made == head else f"main's first-parent chain, position {history.at(made)}"
                 if made and history.at(made) is not None else "unknown")
        print(f"graph: {graph.source}" + (f", a ZIP of sha256 {graph.zip_sha256}" if graph.zip_sha256 else
                                           ", a directory"))
        print(f"  producer: ATLAS {producer or '(none)'} ({where})")
        print(f"  Mathlib pin: {pin or '(none)'}")
        print(f"  stats.json sha256: {graph.stats_sha256}")
        print(f"  nodes.jsonl.gz sha256: {graph.nodes_sha256}")
        print(f"  modules with a node: {len(graph.modules):,}, sorted list sha256 {graph.modules_sha256}")
        print("  identity: compare these digests with those of the CI artifact the graph comes from")
    rows_by_file = collections.Counter(verdict.row.path for verdict in new)
    if record.fresh_known:
        print(f"new fragments: {len(record.fresh)}, {count(len(new), 'row')}")
    else:
        print(f"new fragments: unknown, as main's record at the base cannot be read; the head's fragments hold "
              f"{count(len(new), 'row')}")
    for path, data in record.fresh:
        print(f"  {path}: blob {blob_id(data, history.form)}, sha256 {hashlib.sha256(data).hexdigest()}, "
              f"{count(rows_by_file[path], 'row')}")
    for verdict in new:
        state = (f"honoured, {verdict.how}" if verdict.honoured else f"{verdict.state} ({verdict.reason})")
        print(f"row {verdict.row.where}: {verdict.row.index} -> {verdict.row.to}: {state}; its route at the head "
              f"shows: {MoveRecord.notice_label(verdict.row.index, notices, live)}")
    for line in record.advice(f"python scripts/build_mathlib_pages.py moves --base {base} --graph GRAPH"):
        print(line)
    for warning in record.warnings:
        print(f"warning: {warning}")
    for error in record.errors:
        print(f"error: {error}")
    for prior, reason in record.unresolved:
        print(f"not certified: {'prior record unresolved' if prior else 'unresolved'}: {reason}")
    passing = sum(1 for verdict in new if verdict.honoured)
    if advisory:
        print(f"result: advisory, not a verification of record: {passing} of {count(len(new), 'new row')} pass on "
              "this list" + "".join(f"; and {reason}" for reason in blocking + unknown))
        return ADVISORY
    for reason in blocking:
        print(f"not certified: {reason}")
    if blocking:
        print("result: not certified")
        return REFUSED
    if record.errors:
        # Each new row refused is an error of its own; any other error is the change's, beyond its rows.
        refused = [verdict for verdict in new if verdict.state == "refused"]
        others = [error for error in record.errors if error not in {f"{v.row.where}: {v.reason}" for v in refused}]
        parts = [f"{len(refused)} of {count(len(new), 'new row')} do not pass"] if refused else []
        parts += [f"{count(len(others), 'error')} beyond the new rows"] if others else []
        print(f"result: refused: {'; '.join(parts)}")
        return REFUSED
    for reason in unknown:
        print(f"not certified: unresolved: {reason}")
    if record.unresolved or unknown:
        # Unknown is neither a pass nor a refusal: rerun where the whole record can be read.
        print("result: not certified: " + ("prior record unresolved" if record.prior_unresolved else
                                           "the new rows are unresolved" if record.unresolved else
                                           "what the receipt needs cannot be established here"))
        return UNRESOLVED
    print(f"result: certified: every one of the {count(len(new), 'new row')} passes")
    return CERTIFIED


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    b = commands.add_parser("build", help="write the site with its Mathlib pages")
    b.add_argument("--report", type=Path, help="also write the build report (JSON) here")
    b.add_argument("--strict-links", action="store_true",
                   help="fail when a Mathlib source link does not match its title")
    b.add_argument("--mkdocs", default=f"{sys.executable} -m mkdocs", help="the MkDocs command")
    c = commands.add_parser("check", help="check a site that build wrote")
    for command in (b, c):
        command.add_argument("site", type=Path, help="the built site")
        command.add_argument("graph", type=Path, help="the mathlib-graph artifact of the same revision")
        command.add_argument("out", type=Path, help="the site with its Mathlib pages")
    m = commands.add_parser("moves", help="propose rows for the index routes a change removes (advisory)")
    where = m.add_mutually_exclusive_group(required=True)
    where.add_argument("--base", help="a commit of main: the routes it has that the checkout lacks")
    where.add_argument("--at", help="a commit of main: the routes its first parent has that it lacks")
    m.add_argument("--write", metavar="SLUG", help="write the rows to a new fragment of scripts/mathlib-moves.d")
    m.add_argument("--now", metavar="YYYYMMDDTHHMMSSZ", help="the UTC time the writer takes for now (for tests)")
    k = commands.add_parser("check-moves", help="judge the head commit's new rows as a pull request's check does")
    k.add_argument("--base", required=True, help="the pull request's base, a commit of main")
    for command in (m, k):
        given = command.add_mutually_exclusive_group(required=True)
        given.add_argument("--graph", type=Path,
                           help="a mathlib-graph artifact, a directory or the ZIP CI serves (certifying)")
        given.add_argument("--modules", type=Path, help="a list of modules, one a line (advisory)")
    args = parser.parse_args(argv)
    if args.command == "moves":
        return moves_command(args)
    if args.command == "check-moves":
        return check_moves_command(args)
    pull_request, problem = pull_request_base()
    if args.command == "build":
        report = build(args.site, args.graph, args.out, args.mkdocs.split(), pull_request=pull_request)
        text = json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        if args.report:
            args.report.write_text(text, encoding="utf-8")
        print(text, end="")
        for problem_found in report["problems"]:
            print(f"warning: {problem_found}", file=sys.stderr)
        # The record never fails the build: the check fails on what a pull request's new rows get wrong.
        for warning in ([problem] if problem else []) + report["moves"]["errors"] + report["moves"]["warnings"]:
            print(f"warning: moved index pages: {warning}", file=sys.stderr)
        return 1 if args.strict_links and report["problems"] else 0
    advice: list[str] = []
    errors = ([problem] if problem else []) + check(args.site, args.graph, args.out, pull_request=pull_request,
                                                    advice=advice)
    for line in advice:
        print(line)
    for error in errors[:200]:
        print(error, file=sys.stderr)
    if errors:
        print(f"{len(errors):,} problems", file=sys.stderr)
        # A pull request whose record alone is unresolved is neither passed nor refused.
        return UNRESOLVED if all(error.startswith(NOT_CERTIFIED) for error in errors) else REFUSED
    print("Every page of the site is unchanged apart from its Mathlib links and additions, and every link resolves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
