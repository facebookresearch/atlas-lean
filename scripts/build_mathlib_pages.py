#!/usr/bin/env python3
"""Pages for Mathlib's declarations, built from the Mathlib layer of the dependency graph.

    python scripts/build_mathlib_pages.py build [--strict-links] [--report REPORT.json] SITE GRAPH OUT
    python scripts/build_mathlib_pages.py check SITE GRAPH OUT

`build` reads a built site (the `site` directory the wiki job builds) and the `mathlib-graph` artifact of the same
ATLAS revision (docs/mathlib-layer.md), and writes OUT: the same site plus one page per Mathlib module under
`mathlib/`, grouped by the topics of scripts/taxonomy.json, with the site's links to Mathlib declarations pointed
at those pages and each statement box listing the Mathlib declarations its Lean statement and proof use. `check`
verifies OUT against SITE: every file of SITE is in OUT, unchanged apart from the links and additions `build`
makes, and every link `build` writes resolves to the declaration it names. docs/mathlib-pages.md describes the
pages and the link scheme.

The pages' chrome (header, navigation, footer) comes from MkDocs with the site's own theme: MkDocs renders a
placeholder page for each Mathlib page and the declarations are put in afterwards, since MkDocs would take hours
over the declarations themselves. Nothing this script writes is committed.
"""

from __future__ import annotations

import argparse
import collections
import gzip
import html
import json
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as etree
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import quote, unquote_to_bytes, urlsplit

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


def plan_pages(graph: Graph, hosted: set[int], taxonomy: dict) -> Plan:
    """One page per module with hosted declarations; one per topic with several such modules, else the module's
    page stands for its topic; one per subject, field and subfield; modules outside the taxonomy on their own."""
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
        taken = set(subfields.get(to, ()))
        for topic in sorted((t for t in topic_modules if t[0] == to), key=lambda t: (t[1].casefold(), t[1])):
            modules = topic_modules[topic]
            if len(modules) == 1:
                add_module(container, modules[0], topic[1], topic)
                continue
            slug, number = slugify(topic[1]), 1
            while slug in taken:
                number += 1
                slug = f"{slugify(topic[1])}-{number}"
            taken.add(slug)
            page = Page(f"{SECTION}/{to}/{slug}/index.html", topic[1], topic[1], "topic", modules, topic=topic)
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
# build


def build(site: Path, graph_dir: Path, out: Path, mkdocs: list[str], keep: set[str] | None = None) -> dict:
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
    plan = plan_pages(graph, hosted, taxonomy)
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


def check(site: Path, graph_dir: Path, out: Path) -> list[str]:
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
    args = parser.parse_args(argv)
    if args.command == "build":
        report = build(args.site, args.graph, args.out, args.mkdocs.split())
        text = json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        if args.report:
            args.report.write_text(text, encoding="utf-8")
        print(text, end="")
        for problem in report["problems"]:
            print(f"warning: {problem}", file=sys.stderr)
        return 1 if args.strict_links and report["problems"] else 0
    errors = check(args.site, args.graph, args.out)
    for error in errors[:200]:
        print(error, file=sys.stderr)
    if errors:
        print(f"{len(errors):,} problems", file=sys.stderr)
        return 1
    print("Every page of the site is unchanged apart from its Mathlib links and additions, and every link resolves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
