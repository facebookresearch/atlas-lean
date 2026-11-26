#!/usr/bin/env python3
"""Tests for scripts/build_mathlib_pages.py and scripts/mathlib_link.py on a small site and Mathlib layer."""

from __future__ import annotations

import contextlib
import gzip
import hashlib
import html
import io
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
import warnings
import zipfile
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from unittest import mock
from urllib.parse import urljoin

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_mathlib_pages as pages  # noqa: E402
import card_moves  # noqa: E402
import mathlib_link  # noqa: E402
import pack_pages_site  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
ATLAS = "a" * 40
REV = "b" * 40
TOPIC = "NumberTheory/diophantine-equations"
FOLDER = f"roadmap/{TOPIC}/fixture-topic"
OTHER = f"roadmap/{TOPIC}/other-topic"
MKDOCS = [sys.executable, "-m", "mkdocs"]


def source(module: str, line: int) -> str:
    return f"{pages.MATHLIB_GIT}/blob/{REV}/{module.replace('.', '/')}.lean#L{line}"


def docs_link(name: str) -> str:
    return f'<a class="bp-lean-doc" href="{pages.DOCS_FIND}{name}#doc" title="{name}">{name}</a>'


DIAGRAM = "```lean\n∐ i, X i ⟶ Y\n  ↓     ↓\n```\nA diagram, and `<raw>`."
NODES = [
    # name, module, kind, name_line, doc, signature
    ("Foo", "Mathlib.Foo.Basic", "structure", 5,
     "A *foo*, see `Foo.bar`, <b>not bold</b>, [no script](javascript:alert(1)), $x^2$ and "
     "[Foo.bar](https://github.com/leanprover-community/mathlib4/blob/master/README.md).", "Foo : Type"),
    ("Foo.bar", "Mathlib.Foo.Basic", "theorem", 12, DIAGRAM, "Foo.bar (x : Foo) : x = x"),
    ("Foo.inst", "Mathlib.Foo.Basic", "instance", 20, "", "Foo.inst : Inhabited Foo"),
    ("Baz.qux?", "Mathlib.Baz", "definition", 3, "", "Baz.qux? : Option Foo"),
    ("Baz.qux'", "Mathlib.Baz", "theorem", 4, "", "Baz.qux' : Baz.qux? = none"),
    ("Old.thing", "Mathlib.Old", "theorem", 7, "", "Old.thing : True"),
]
EDGES = [
    ("Foo.bar", "Foo", "statement"),
    ("Foo.bar", "Foo.inst", "proof"),
    ("Baz.qux'", "Baz.qux?", "statement"),
    ("Baz.qux?", "Foo", "statement"),
    ("Old.thing", "Foo.bar", "proof"),
]
BRIDGE = [
    ("Atlas.one", "Foo.bar", "statement"),
    ("Atlas.one", "Baz.qux'", "proof"),
    ("Atlas.one", "Foo.inst", "proof"),
    ("Atlas.two", "Foo", "statement"),
    ("Atlas.hidden", "Foo", "statement"),
    ("Atlas.three", "Foo", "statement"),
    ("Atlas.four", "Foo", "statement"),
    ("Atlas.dup", "Baz.qux?", "statement"),
    ("Atlas.solo", "Foo", "proof"),
    ("Atlas.m1", "Foo", "statement"),
    ("Atlas.m2", "Baz.qux'", "proof"),
    ("Atlas.five", "Foo", "statement"),
    ("Atlas.six", "Foo", "statement"),
    ("Atlas.seven", "Foo", "statement"),
]


def write_jsonl(path: Path, rows) -> None:
    with gzip.open(path, "wt", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def make_graph(root: Path) -> Path:
    graph = root / "graph"
    graph.mkdir()
    (graph / "stats.json").write_text(json.dumps({"versions": {"mathlib_rev": REV, "atlas_commit": ATLAS}}))
    write_jsonl(graph / "nodes.jsonl.gz", [
        {"name": n, "module": m, "kind": k, "line": line, "name_line": line, "doc": doc, "signature": sig}
        for n, m, k, line, doc, sig in NODES
    ])
    topics = []
    for name, module, *_ in NODES:
        if module == "Mathlib.Old":
            topics.append({"name": name, "key": "Mathlib/Old", "placement": "Mathlib/Old", "exclude": "an old module"})
        else:
            key = module.replace(".", "/")
            topics.append({"name": name, "key": key, "placement": key, "to": TOPIC, "title": "Fixture topic"})
    write_jsonl(graph / "topics.jsonl.gz", topics)
    write_jsonl(graph / "edges.jsonl.gz", [{"source": s, "target": t, "kind": k} for s, t, k in EDGES])
    write_jsonl(graph / "bridge-edges.jsonl.gz", [{"source": s, "target": t, "kind": k} for s, t, k in BRIDGE])
    return graph


def build_mkdocs(docs: Path, site: Path, summary: str) -> None:
    (docs / "SUMMARY.md").write_text(summary)
    config = docs.parent / f"{site.name}.yml"
    config.write_text("\n".join([
        f"INHERIT: {json.dumps(str(ROOT / 'mkdocs.yml'))}",
        f"docs_dir: {json.dumps(str(docs))}",
        f"site_dir: {json.dumps(str(site))}",
        "theme:",
        "  name: material",
        f"  custom_dir: {json.dumps(str(ROOT / 'theme'))}",
        "hooks:",
        f"  - {json.dumps(str(ROOT / 'hooks' / 'title_only_search.py'))}",
        f"  - {json.dumps(str(ROOT / 'hooks' / 'trim_pages.py'))}",
        "",
    ]))
    subprocess.run([*MKDOCS, "build", "--strict", "--quiet", "--config-file", str(config)], check=True)


def card(node: str, anchor: str, inner: str, status: str = "bp-fully_proved") -> str:
    return (f'<div class="bp-thmwrapper theorem-style-plain {status}" data-autoform-node-id="{TOPIC}/{node}" '
            f'data-autoform-result="">\n<h4 class="bp-thmheading" id="{anchor}">Title of {anchor}</h4>\n{inner}\n</div>')


def mathlib_meta(name: str) -> str:
    return f'<div class="bp-meta"><div class="bp-row"><span class="bp-key">Mathlib</span><span class="bp-value"><code>{name}</code></span></div></div>'


TOPIC_CARDS = "\n".join([
    card("fixture-topic/one", "one", f"""<div class="bp-lean-source"><pre class="bp-lean"><code>theorem one : {docs_link("Foo.bar")} = {docs_link("Nat")}</code></pre></div>
<p>See <a href="{source("Mathlib.Baz", 3)}" title="Baz.qux?">the query</a>, <a href="{source("Mathlib.Baz", 9)}" title="Foo.bar">a wrong one</a> and <a href="{pages.DOCS_FIND}Foo#doc">prose</a>.</p>
<details class="bp-dependencies">
<summary>Used by 1</summary>
<div class="bp-dependency-body">
<div class="bp-row"><span class="bp-key">Used by</span><span class="bp-value"><a class="bp-ref" href="#two">Article two</a></span></div>
</div>
</details>"""),
    card("fixture-topic/two", "two", mathlib_meta("Foo.bar"), "bp-mathlib"),
    # The catalog sends "three" to this anchor, but its heading says otherwise.
    card("fixture-topic/three", "tres", ""),
    card("fixture-topic/dup1", "dup1", ""),
    card("fixture-topic/dup2", "dup2", ""),
    card("fixture-topic/multi", "multi", ""),
    # Two boxes share one heading id, and a box whose own heading has no id has a notes heading with its anchor.
    card("fixture-topic/five", "shared", ""),
    card("fixture-topic/six", "shared", ""),
    f'<div class="bp-thmwrapper theorem-style-plain bp-fully_proved" data-autoform-node-id="{TOPIC}/fixture-topic/seven">'
    '<h4 class="bp-thmheading">Seven</h4><h6 id="seven">Notes</h6></div>',
    '<p>A literal marker in code: <code>&lt;a data-ml="a"&gt;</code>, data-ml="a".</p>',
])
# A copy of article two's box on a page the catalog does not send it to.
OTHER_CARDS = card("fixture-topic/two", "two", mathlib_meta("Baz.qux'"), "bp-mathlib")
HOME_HERO = '<div class="bp-hero"><div class="bp-hero-coverage"><span>4 of 8</span></div></div>'
SOLO = f'<div class="bp-reading-source" data-autoform-node-id="{TOPIC}/fixture-topic/solo" data-page-title="Solo">'


def make_site(root: Path) -> Path:
    docs, site = root / "src", root / "site"
    for path, text in {
        "assets/autoform.svg": '<svg xmlns="http://www.w3.org/2000/svg"/>',
        "stylesheets/blueprint.css": "",
        "javascripts/mathjax.js": "",
        "javascripts/blueprint-mermaid.js": "",
        "index.md": "# Home\n\nHOME\n",
        f"{FOLDER}/README.md": "# Fixture topic\n\nCARDS\n",
        f"{OTHER}/README.md": "# Other topic\n\nCARDS\n",
        f"{FOLDER}/solo.md": "# Solo\n\nSOLO\n",
    }.items():
        (docs / path).parent.mkdir(parents=True, exist_ok=True)
        (docs / path).write_text(text)
    build_mkdocs(docs, site, f"- [Home](index.md)\n- [Fixture topic]({FOLDER}/README.md)\n"
                             f"    - [Solo]({FOLDER}/solo.md)\n- [Other topic]({OTHER}/README.md)\n")
    for path, old, new in (("index.html", "<p>HOME</p>", HOME_HERO),
                           (f"{FOLDER}/index.html", "<p>CARDS</p>", TOPIC_CARDS),
                           (f"{OTHER}/index.html", "<p>CARDS</p>", OTHER_CARDS),
                           (f"{FOLDER}/solo.html", "<p>SOLO</p>", SOLO + "<p>On its own page.</p></div>")):
        (site / path).write_text((site / path).read_text().replace(old, new))
    (site / "publication.json").write_text(json.dumps({"git_ref": ATLAS}))
    route = f"../{FOLDER}/index.html"

    def article(name, lean, status="fully_proved"):
        return {"id": f"{TOPIC}/fixture-topic/{name}", "kind": "node", "lean": lean, "route": f"{route}#{name}",
                "title": f"Article {name}", "status": status}

    catalog = {"nodes": [
        {"id": "roadmap", "kind": "scope", "route": "../roadmap/index.html", "title": "ATLAS roadmap", "status": "planned"},
        {"id": TOPIC, "kind": "scope", "route": f"../roadmap/{TOPIC}/index.html", "title": "Diophantine equations",
         "status": "planned"},
        {"id": f"{TOPIC}/fixture-topic", "kind": "scope", "route": route, "title": "Fixture topic", "status": "planned"},
        article("one", "Atlas.one"), article("two", "Atlas.two", "mathlib"), article("three", "Atlas.three"),
        article("four", "Atlas.four"), article("dup1", "Atlas.dup"), article("dup2", "Atlas.dup"),
        article("multi", "Atlas.m1, Atlas.m2"),
        article("five", "Atlas.five"), article("six", "Atlas.six"), article("seven", "Atlas.seven"),
        {"id": f"{TOPIC}/fixture-topic/solo", "kind": "node", "lean": "Atlas.solo", "route": f"../{FOLDER}/solo.html",
         "title": "Article solo", "status": "can_state"},
    ]}
    (site / "dependencies").mkdir()
    (site / "dependencies" / "index.json").write_text(json.dumps(catalog))
    return site


def quiet_build(*args, **kwargs):
    with contextlib.redirect_stdout(io.StringIO()):
        return pages.build(*args, **kwargs)


class PageTexts(HTMLParser):
    """The decoded text of a page's title in its head (the `<title>` there alone), its header, its heading and its own
    navigation link."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.open: list[tuple[str, str | None]] = []
        self.found: dict[str, str] = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        key = ("head" if tag == "title" and any(name == "head" for name, _ in self.open)
               else "heading" if tag == "h1" and attrs.get("id") == "_title"
               else "header" if attrs.get("data-md-component") == "header-topic"
               else "navigation" if tag == "a" and attrs.get("href") == "index.html"
               and "md-nav__link--active" in (attrs.get("class") or "").split() else None)
        self.open.append((tag, key))
        if key:
            self.found.setdefault(key, "")

    def handle_endtag(self, tag):
        while self.open and self.open.pop()[0] != tag:
            pass

    def handle_data(self, data):
        for _, key in self.open:
            if key:
                self.found[key] += data


class MathlibPagesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        root = Path(cls.directory.name)
        # The fixture site has a record of moved index pages of its own, empty, not the repository's.
        cls.no_record = mock.patch.object(pages, "RECORD_ROOT", root / "no-record")
        cls.no_record.start()
        cls.graph, cls.site, cls.out = make_graph(root), make_site(root), root / "out"
        cls.report = quiet_build(cls.site, cls.graph, cls.out, MKDOCS)

    @classmethod
    def tearDownClass(cls):
        cls.no_record.stop()
        cls.directory.cleanup()

    def read(self, path: str, root: Path | None = None) -> str:
        return ((root or self.out) / path).read_text(encoding="utf-8")

    def tampered(self, edit) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory) / "out"
            shutil.copytree(self.out, copy)
            edit(copy)
            return pages.check(self.site, self.graph, copy)

    def test_the_site_leaves_out_the_bump_records_and_no_topic(self):
        # A topic folder is named after its title, which the taxonomy chooses: an exclusion of the site that matched
        # at any depth would drop its pages. MkDocs loads the configured exclusions, and there is one.
        from mkdocs.config import load_config

        with tempfile.TemporaryDirectory() as docs, tempfile.TemporaryDirectory() as site:
            excluded = load_config(str(ROOT / "mkdocs.yml"), docs_dir=docs, site_dir=site)["exclude_docs"]
        self.assertEqual([rule.pattern for rule in excluded.patterns if rule.include is not None], ["/migrations/"])
        self.assertTrue(excluded.match_file("migrations/README.md"))
        self.assertTrue(excluded.match_file("migrations/2026-11-01-bump.md"))
        for page in ("mathlib/Algebra/algebraic-identities/migrations/index.md",
                     "roadmap/Algebra/x/migrations/README.md", "roadmap/migrations/README.md"):
            self.assertFalse(excluded.match_file(page), page)

    def test_a_title_with_markup_characters_reads_as_text(self):
        # The taxonomy titles topics: a title such as `Maps on List<T>`, one that holds an element or a link, a
        # control character, or a half-open interval followed by a colon, reads as its own text in the page's head,
        # header, heading and navigation, and in the search index (escaped once, as the theme's results take it),
        # and leaves the site's check nothing to follow.
        for title, folder in (('Maps on List<T> & <img src="diagram.svg"> Bayes\x92 rule [notes](notes.md)',
                               "maps-on-list"),
                              ("Integrals on (a,b]: basics", "integrals-on-a-b")):
            with self.subTest(title=title), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                graph, site, out = make_graph(root), make_site(root), root / "out"
                with gzip.open(graph / "topics.jsonl.gz", "rt", encoding="utf-8") as handle:
                    topics = [json.loads(line) for line in handle]
                write_jsonl(graph / "topics.jsonl.gz",
                            [{**row, "title": title} if "title" in row else row for row in topics])
                quiet_build(site, graph, out, MKDOCS)
                self.assertEqual(pages.check(site, graph, out), [])
                page = next(path for path in out.rglob("index.html") if path.parent.name.startswith(folder))
                texts = PageTexts()
                texts.feed(page.read_text(encoding="utf-8"))
                self.assertEqual({key: " ".join(value.split()) for key, value in texts.found.items()},
                                 {"head": f"{title} - ATLAS", "header": title, "heading": title, "navigation": title})
                index = json.loads((out / pages.SEARCH_INDEX).read_text(encoding="utf-8"))
                record = next(doc for doc in index["docs"] if doc["location"] == page.relative_to(out).as_posix())
                self.assertEqual(record["title"], html.escape(title, quote=False))

    def test_the_committed_taxonomy_titles_and_describes_every_group(self):
        # (Its placements' titles, the topics' names in the navigation too, are one line each: see
        # scripts/test_blueprint_taxonomy.py.)
        # The page plan reads scripts/taxonomy.json itself: a PR that changes only the taxonomy skips the Mathlib
        # pages' build, so its unit tests catch a subject, field or subfield the pages could not title or describe.
        titles, descriptions, order, _ = pages.taxonomy_tree(json.loads(pages.TAXONOMY.read_text(encoding="utf-8")))
        self.assertTrue(order)
        # A title is one line: it labels the group in the site's navigation, whose entries are lines.
        self.assertEqual([path for path in order if not isinstance(titles[path], str) or not titles[path].strip()
                          or titles[path].splitlines() != [titles[path]]], [])
        self.assertEqual([path for path in order if not isinstance(descriptions[path], str)], [])

    def test_one_page_per_module_grouped_by_topic(self):
        self.assertEqual(self.report["declarations"], len(NODES))
        self.assertEqual(self.report["modules"], 3)
        for path in ("mathlib/index.html", f"mathlib/{TOPIC}/index.html", f"mathlib/{TOPIC}/fixture-topic/index.html",
                     "mathlib/Foo.Basic.html", "mathlib/Baz.html", "mathlib/outside/index.html", "mathlib/Old.html"):
            self.assertTrue((self.out / path).is_file(), path)
        topic = self.read(f"mathlib/{TOPIC}/fixture-topic/index.html")
        self.assertIn('href="../../../Foo.Basic.html"', topic)
        self.assertIn('href="../../../Baz.html"', topic)
        self.assertIn('href="../../../../roadmap/NumberTheory/diophantine-equations/fixture-topic/index.html"', topic)
        self.assertIn("an old module", self.read("mathlib/Old.html"))

    def test_rows_show_statement_docstring_and_edges(self):
        foo = self.read("mathlib/Foo.Basic.html")
        self.assertIn('<div class="ml-decl" id="Foo.bar">', foo)
        self.assertIn('<pre class="ml-sig"><code>(x : Foo) : x = x</code></pre>', foo)
        self.assertIn(f'href="{source("Mathlib.Foo.Basic", 12)}"', foo)
        self.assertIn('<b>Statement uses</b> <a href="#Foo">Foo</a></p>', foo)
        self.assertIn("<b>Proof uses</b> <span class=\"ml-inst\">instances: <code>Foo.inst</code></span>", foo)
        self.assertIn('<a href="Old.html#Old.thing">Old.thing</a>', foo)
        self.assertIn(f'<a href="../{FOLDER}/index.html#one">Article one</a>', foo)
        self.assertIn(f'<b>Stated in ATLAS as</b> <a href="../{FOLDER}/index.html#two">Article two</a>', foo)

    def test_docstrings_are_markdown_without_html_or_script_links(self):
        foo = self.read("mathlib/Foo.Basic.html")
        self.assertIn("<em>foo</em>", foo)
        self.assertIn('<code><a href="#Foo.bar">Foo.bar</a></code>', foo)
        self.assertIn("&lt;b&gt;not bold&lt;/b&gt;", foo)
        self.assertNotIn("javascript:", foo)
        self.assertIn('<span class="arithmatex">\\(x^2\\)</span>', foo)
        self.assertIn('<pre><code class="language-lean">∐ i, X i ⟶ Y\n  ↓     ↓\n</code></pre>', foo)
        self.assertIn("<code>&lt;raw&gt;</code>", foo)

    def test_names_with_question_marks_and_apostrophes_link_and_resolve(self):
        baz = self.read("mathlib/Baz.html")
        self.assertIn('id="Baz.qux?"', baz)
        self.assertIn('id="Baz.qux&#x27;"', baz)
        self.assertIn('href="#Baz.qux%3F"', baz)
        self.assertIn('href="#Baz.qux%27"', baz)

    def test_the_site_links_to_the_pages_and_lists_the_mathlib_uses(self):
        topic = self.read(f"{FOLDER}/index.html")
        self.assertIn('href="../../../../mathlib/Foo.Basic.html#Foo.bar" title="Foo.bar" data-ml="d"', topic)
        self.assertIn(f'href="{pages.DOCS_FIND}Nat#doc" title="Nat">', topic)
        self.assertIn('href="../../../../mathlib/Baz.html#Baz.qux%3F" title="Baz.qux?" data-ml="a"', topic)
        self.assertIn(f'href="{source("Mathlib.Baz", 9)}" title="Foo.bar">a wrong one', topic)
        # A documentation link in prose is not Autoform's: it stays.
        self.assertIn(f'<a href="{pages.DOCS_FIND}Foo#doc">prose</a>', topic)
        self.assertEqual(len(self.report["problems"]), 1)
        self.assertIn("<summary>Used by 1<span class=\"ml-sum\"> · Mathlib 2</span></summary>", topic)
        self.assertIn('<span class="bp-key">Mathlib, statement</span><span class="bp-value"><a class="bp-ref bp-ref-mathlib" '
                      'href="../../../../mathlib/Foo.Basic.html#Foo.bar">Foo.bar</a></span>', topic)
        self.assertIn('<span class="bp-key">Mathlib, proof</span>', topic)
        self.assertNotIn(">Foo.inst</a>", topic)
        self.assertIn('<details class="bp-dependencies ml-added"><summary>Mathlib 1</summary>', topic)
        self.assertIn('data-ml="c"><code>Foo.bar</code></a>', topic)
        self.assertIn('href="mathlib/index.html">Mathlib pages</a>', self.read("index.html"))
        search = json.loads(self.read("search/search_index.json"))
        self.assertIn("mathlib/Foo.Basic.html", [doc["location"] for doc in search["docs"]])

    def test_only_published_statement_boxes_count(self):
        # Atlas.hidden has no catalog entry, three's heading is not its route's anchor, four has no box, and a copy of
        # two's box on another page is not two's: none of them is named, credited or enriched.
        for path in self.out.rglob("*.html"):
            text = path.read_text(encoding="utf-8")
            for hidden in ("Article three", "Article four", "Atlas.hidden"):
                self.assertNotIn(hidden, text, path)
        self.assertEqual(self.report["catalog_articles_not_published"], 5)
        for unpublished in ("Article five", "Article six", "Article seven"):
            self.assertNotIn(unpublished, self.read("mathlib/Foo.Basic.html"))
        other = self.read(f"{OTHER}/index.html")
        self.assertEqual(other, self.read(f"{OTHER}/index.html", self.site))
        self.assertNotIn("Stated in ATLAS as", self.read("mathlib/Baz.html"))
        # Two articles of one Lean name are both its users; an article with two names uses what both use; an article
        # on its own page is linked without an anchor; proof-only users are counted as such.
        baz = self.read("mathlib/Baz.html")
        self.assertIn('<b>Used in ATLAS by</b> 2 statements: <a href="../roadmap/', baz)
        self.assertIn('<b>Used in ATLAS by</b> 2 proofs: <a href="../roadmap/', baz)
        foo = self.read("mathlib/Foo.Basic.html")
        self.assertIn(f'<a href="../{FOLDER}/solo.html">Article solo</a>', foo)
        self.assertIn('Article multi</a>', foo)
        topic = self.read(f"{FOLDER}/index.html")
        multi = topic[topic.index('id="multi"'):]
        self.assertIn("Foo.Basic.html#Foo\">Foo</a>", multi.split("</details>")[0])
        self.assertIn("Baz.html#Baz.qux%27\">Baz.qux&#x27;</a>", multi.split("</details>")[0])
        tres = self.read(f"{FOLDER}/index.html")
        self.assertNotIn('id="tres">Title of tres</h4>\n<details', tres)

    def test_check_accepts_the_build_and_restores_every_page(self):
        self.assertEqual(pages.check(self.site, self.graph, self.out), [])

    def test_check_finds_changes_beyond_the_additions(self):
        def edit(copy: Path) -> None:
            topic = copy / FOLDER / "index.html"
            topic.write_text(topic.read_text().replace("Title of one</h4>", "Title of 1</h4>"))
            (copy / "extra.html").write_text("x")
            (copy / "mathlib" / "Baz.html").unlink()

        errors = self.tampered(edit)
        self.assertTrue(any("changed beyond the Mathlib links" in e for e in errors), errors)
        self.assertTrue(any(e.startswith("extra.html: added outside") for e in errors), errors)
        self.assertTrue(any("Baz.html" in e and "names no file" in e for e in errors), errors)

    def test_check_resolves_every_addition(self):
        def edit(copy: Path) -> None:
            home = copy / "index.html"
            home.write_text(home.read_text().replace('href="mathlib/index.html"', 'href="mathlib/nowhere.html"'))
            topic = copy / FOLDER / "index.html"
            topic.write_text(topic.read_text().replace('Foo.Basic.html#Foo.bar">Foo.bar</a></span>',
                                                       'Foo.Basic.html#Foo.nothing">Foo.bar</a></span>'))
            index = copy / "search" / "search_index.json"
            search = json.loads(index.read_text())
            search["docs"].append({"location": "mathlib/nowhere-else.html", "text": "", "title": "x"})
            index.write_text(json.dumps(search))

        errors = self.tampered(edit)
        self.assertTrue(any(e.startswith("index.html: mathlib/nowhere.html names no file") for e in errors), errors)
        self.assertTrue(any("#Foo.nothing names no anchor" in e for e in errors), errors)
        self.assertTrue(any("mathlib/nowhere-else.html names no file" in e for e in errors), errors)

    def test_check_requires_each_link_to_lead_to_its_declaration(self):
        def edit(copy: Path) -> None:
            topic = copy / FOLDER / "index.html"
            text = topic.read_text()
            text = text.replace('Foo.Basic.html#Foo.bar">Foo.bar</a></span>', 'Foo.Basic.html#Foo">Foo.bar</a></span>')
            # A Mathlib use that leads to an ATLAS heading of the same name.
            text = text.replace('mathlib/Baz.html#Baz.qux%27">Baz.qux&#x27;</a>', 'mathlib/Foo.Basic.html#Baz.qux%27">Baz.qux&#x27;</a>')
            mathlib = copy / "mathlib" / "Baz.html"
            mathlib.write_text(mathlib.read_text().replace('<a href="Foo.Basic.html#Foo">Foo</a>', '<a href="../roadmap/'
                               'NumberTheory/diophantine-equations/fixture-topic/index.html#one">Foo</a>'))
            text = text.replace('Baz.html#Baz.qux%3F" title="Baz.qux?" data-ml="a"', 'Baz.html#Baz.qux%27" title="Baz.qux?" data-ml="a"')
            text = text.replace('Foo.Basic.html#Foo.bar" data-ml="c"', 'Foo.Basic.html#Foo" data-ml="c"')
            topic.write_text(text)

        errors = self.tampered(edit)
        self.assertTrue(any("the link to Foo.bar leads to" in e for e in errors), errors)
        self.assertTrue(any("titled 'Baz.qux?' leads to" in e for e in errors), errors)
        self.assertTrue(any("the link to Foo.bar leads to" in e and "data-ml" not in e for e in errors), errors)
        self.assertTrue(any("the link to Baz.qux' leads to" in e for e in errors), errors)
        self.assertTrue(any(e.startswith("mathlib/Baz.html: the link to Foo leads to") for e in errors), errors)
        # The docstring's own link, named like a declaration, is not the build's: it is not judged.
        self.assertFalse(any("README.md" in e for e in errors), errors)

    def test_partial_hosting_counts_what_it_does_not_show(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "out"
            report = quiet_build(self.site, self.graph, out, MKDOCS, keep={"Foo", "Baz.qux?"})
            topic = self.read(f"{FOLDER}/index.html", out)
            baz = self.read("mathlib/Baz.html", out)
            self.assertEqual(pages.check(self.site, self.graph, out), [])
        self.assertEqual(report["declarations"], 2)
        # A declaration without a page here links to its pinned source line, and is counted where it is listed.
        self.assertIn('<span class="bp-key">Mathlib, statement</span><span class="bp-value"><a class="bp-ref '
                      f'bp-ref-mathlib" href="{source("Mathlib.Foo.Basic", 12)}">Foo.bar</a></span>', topic)
        self.assertIn(f'href="{pages.DOCS_FIND}Foo.bar#doc" title="Foo.bar">', topic)
        self.assertIn(f'<a href="{source("Mathlib.Baz", 4)}">Baz.qux&#x27;</a>', baz)

    def test_the_build_is_deterministic(self):
        with tempfile.TemporaryDirectory() as directory:
            again = Path(directory) / "out"
            quiet_build(self.site, self.graph, again, MKDOCS)
            first = {p.relative_to(self.out): p.read_bytes() for p in self.out.rglob("*") if p.is_file()}
            second = {p.relative_to(again): p.read_bytes() for p in again.rglob("*") if p.is_file()}
        self.assertEqual(first.keys(), second.keys())
        self.assertEqual([p for p in first if first[p] != second[p]], [])

    def test_a_site_of_another_revision_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            graph = Path(directory) / "graph"
            shutil.copytree(self.graph, graph)
            (graph / "stats.json").write_text(json.dumps({"versions": {"mathlib_rev": REV, "atlas_commit": "c" * 40}}))
            with self.assertRaises(SystemExit):
                pages.build(self.site, graph, Path(directory) / "out", MKDOCS)

    def test_strict_links_fail_on_a_mismatched_source_link(self):
        with tempfile.TemporaryDirectory() as directory:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                status = pages.main(["build", "--strict-links", str(self.site), str(self.graph), str(Path(directory) / "o")])
        self.assertEqual(status, 1)

    def test_mathlib_link_prints_the_pinned_source_link(self):
        printed, missing = mathlib_link.links(self.graph, ["Baz.qux?", "Nat.succ"])
        self.assertEqual(printed, [f'[Baz.qux?]({source("Mathlib.Baz", 3)} "Baz.qux?")'])
        self.assertEqual(len(missing), 1)


# ---------------------------------------------------------------------------------------------------------------
# Moved index pages: the record of scripts/mathlib-moves.d, judged on repositories of a few commits


MODULES = ["Mathlib.A1", "Mathlib.A2", "Mathlib.B1", "Mathlib.B2", "Mathlib.C1", "Mathlib.C2"]
ALPHA, BETA, GAMMA = MODULES[0:2], MODULES[2:4], MODULES[4:6]
PLANNER_BYTES = (ROOT / "scripts" / "build_mathlib_pages.py").read_bytes()


def taxonomy(fields: dict, topics: dict, titles: dict | None = None, subject: str = "S",
             excluded: dict | None = None) -> dict:
    """A taxonomy of one subject with ``fields`` ({slug: [subfield slugs]}), its topics ({title: (to, modules)}) and
    its exclusions ({module: reason}); ``titles`` names fields and subfields by path below the subject."""
    titles = titles or {}
    return {
        "subjects": {subject: {"title": f"Subject {subject}", "description": "", "fields": [
            {"slug": slug, "title": titles.get(slug, f"Field {slug}"), "description": "",
             "subfields": [{"slug": sub, "title": titles.get(f"{slug}/{sub}", f"Subfield {sub}"), "description": ""}
                           for sub in subs]}
            for slug, subs in fields.items()]}},
        "placements": {module.replace(".", "/"): {"to": to, "title": title}
                       for title, (to, modules) in topics.items() for module in modules},
        "mathlib_exclusions": {module.replace(".", "/"): reason for module, reason in (excluded or {}).items()},
    }


def move(index: str, existed_at: str, kind: str, title: str, modules, to: str) -> dict:
    return {"index": index, "existed_at": existed_at, "kind": kind, "title": title, "modules": sorted(modules),
            "to": to}


def stamp(graph: Path, site: Path, commit: str) -> None:
    """The fixture graph and site as of ``commit``: the record's tools read the graph's producer there."""
    (graph / "stats.json").write_text(json.dumps({"versions": {"mathlib_rev": REV, "atlas_commit": commit}}))
    (site / "publication.json").write_text(json.dumps({"git_ref": commit}))


def manifest(rev: str) -> str:
    return json.dumps({"version": "1.1.0", "packages": [
        {"url": "https://github.com/leanprover-community/mathlib4", "type": "git", "rev": rev, "name": "mathlib",
         "inputRev": "v0"}]}) + "\n"


class Repo:
    """A repository whose commits hold a taxonomy, this planner, the universe inputs and the record."""

    def __init__(self, root: Path):
        self.root = root
        root.mkdir(parents=True, exist_ok=True)
        self.git("init", "-q", "-b", "main")
        for key, value in (("user.email", "atlas@example.com"), ("user.name", "ATLAS"), ("commit.gpgsign", "false")):
            self.git("config", key, value)
        # This planner and the scripts it imports, as they are, and stand-ins for the other universe inputs.
        self.files = {path: (ROOT / path).read_bytes() for path in (
            "scripts/build_mathlib_pages.py", "scripts/card_moves.py", "scripts/extract_mathlib_graph.py",
            "scripts/extract_v2_lean_dependencies.py")}
        self.files.update({"lake-manifest.json": manifest("1" * 40), "lean-toolchain": "leanprover/lean4:v1\n",
                           "scripts/dump_mathlib_dependencies.lean": "-- dump\n"})
        self.made = 0

    def git(self, *arguments: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *arguments], check=True, capture_output=True,
                              text=True).stdout.strip()

    def fragment(self, rows: list[dict], slug: str = "moves", stamp: str | None = None) -> str:
        """A new fragment of ``rows`` in the working tree, stamped after every earlier one unless ``stamp`` says."""
        self.made += 1
        name = f"{stamp or f'20261101T0000{self.made:02d}Z'}-{slug}.jsonl"
        path = self.root / pages.MOVES / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")
        return f"{pages.MOVES}/{name}"

    def write(self, tree: dict | None = None, rows: list[dict] | None = None, **fragment) -> str | None:
        for path, data in self.files.items():
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_bytes(data if isinstance(data, bytes) else data.encode())
        if tree is not None:
            (self.root / "scripts" / "taxonomy.json").write_text(json.dumps(tree, indent=1), encoding="utf-8")
        return self.fragment(rows, **fragment) if rows else None

    def clear(self) -> None:
        """Remove the working tree's fragments."""
        for path in (self.root / pages.MOVES).glob("*") if (self.root / pages.MOVES).is_dir() else []:
            path.unlink()

    def commit(self, tree: dict | None = None, rows: list[dict] | None = None, **fragment) -> str:
        self.write(tree, rows, **fragment)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "change")
        return self.git("rev-parse", "HEAD")

    def judge(self, base: str | None = None, strict: bool = False, modules=MODULES) -> pages.MoveRecord:
        root = self.git("rev-list", "--max-parents=0", "HEAD")
        with mock.patch.object(pages, "PAGES_SINCE", root):
            record = pages.MoveRecord(modules, checkout=self.root, base=base, strict=strict)
            record.live = record.plan(record.head, record.reserved)
            record.notes = record.notices(record.live, set(modules))
        return record


def run_main(repo: Repo, since: str, argv: list[str]) -> tuple[int, str]:
    """A command of the script run in ``repo``, the Mathlib pages starting at ``since``: its status and its output."""
    printed = io.StringIO()
    with mock.patch.object(pages, "RECORD_ROOT", repo.root), mock.patch.object(pages, "PAGES_SINCE", since), \
            contextlib.redirect_stdout(printed), contextlib.redirect_stderr(printed):
        status = pages.main(argv)
    return status, printed.getvalue()


def graph_zip(path: Path, members: list) -> Path:
    """A ZIP of ``members``, (name or ZipInfo, bytes or a file), in order, duplicates kept."""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", UserWarning)  # zipfile warns of a duplicate name
        with zipfile.ZipFile(path, "w") as archive:
            for name, data in members:
                archive.writestr(name, data if isinstance(data, bytes) else data.read_bytes())
    return path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def graph_inputs(directory: Path, modules: list[str], producer: str, rev: str = "1" * 40) -> Path:
    """A mathlib-graph artifact's stats.json and nodes.jsonl.gz: one node in each of ``modules``."""
    directory.mkdir(parents=True)
    (directory / "stats.json").write_text(json.dumps({"versions": {"atlas_commit": producer, "mathlib_rev": rev}}))
    write_jsonl(directory / "nodes.jsonl.gz", [{"name": f"{module}.x", "module": module} for module in modules])
    return directory


# Alpha in field f, Beta in field g: the routes S, S/f, S/f/alpha, S/g, S/g/beta and the root.
START = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)})
MOVED = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/g", ALPHA), "Beta": ("S/g", BETA)})


class MoveRecordTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Repo(Path(directory.name) / "repo")

    def verdicts(self, record: pages.MoveRecord) -> dict[str, pages.Verdict]:
        return {verdict.row.where: verdict for verdict in record.verdicts}

    def test_a_row_for_an_unchanged_topic_is_refused_and_a_truly_delayed_one_reserves_its_route(self):
        # Alpha is where it was, so a row cannot say it moved, on main or in a pull request.
        repo = self.repo
        c0 = repo.commit(START)
        unchanged = move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/beta")
        repo.write(START, [unchanged])
        record = repo.judge(base=c0, strict=True)
        self.assertEqual(len(record.errors), 1, record.errors)
        self.assertIn("S/f/alpha is live at the checkout", record.errors[0])
        self.assertIn("it did not move", record.errors[0])
        repo.git("add", "-A")
        repo.git("commit", "-q", "-m", "unchanged")
        record = repo.judge()
        self.assertEqual([v.honoured for v in record.verdicts], [False])
        self.assertEqual(record.errors, [])
        self.assertTrue(any("it did not move" in warning for warning in record.warnings), record.warnings)
        self.assertIn("S/f/alpha", record.live)
        self.assertEqual(record.notes[0], {})
        # A truly delayed row: Alpha moved without a row, which a later change adds; it passes, and Alpha's return
        # takes the next free route.
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        repo = Repo(Path(directory.name) / "delayed")
        c0 = repo.commit(START)
        repo.commit(MOVED)
        delayed = repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        record = repo.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.honoured, verdict.how, verdict.judged_at, verdict.plain),
                         (True, "recomputed", delayed, False))
        self.assertEqual(record.notes[0]["S/f/alpha"].target, "mathlib/S/g/alpha/index.html")
        self.assertTrue(record.notes[0]["S/f/alpha"].automatic)
        repo.commit(START)
        record = repo.judge()
        self.assertEqual(record.live["S/f/alpha-2"], pages.Owner("topic", "Alpha", tuple(ALPHA)))
        self.assertNotIn("S/f/alpha", record.live)

    def test_rows_that_would_justify_each_other_are_refused_together(self):
        # ALPHA and Alpha share a folder name: ALPHA holds S/f/alpha, Alpha S/f/alpha-2. With both routes reserved,
        # both topics would move on and each route would be free, but P0 leaves the fragment's rows out.
        repo = self.repo
        tree = taxonomy({"f": []}, {"ALPHA": ("S/f", BETA), "Alpha": ("S/f", ALPHA)})
        c0 = repo.commit(tree)
        rows = [move("S/f/alpha", c0, "topic", "ALPHA", BETA, "Mathlib.B1"),
                move("S/f/alpha-2", c0, "topic", "Alpha", ALPHA, "Mathlib.A1")]
        repo.commit(tree, rows)
        record = repo.judge()
        self.assertEqual([v.honoured for v in record.verdicts], [False, False])
        self.assertTrue(all("it did not move" in v.reason for v in record.verdicts), record.verdicts)
        both = record.plan(record.head, {"S/f/alpha", "S/f/alpha-2"})
        self.assertFalse({"S/f/alpha", "S/f/alpha-2"} & set(both), both)

    def test_both_histories_bring_alpha_back_at_alpha_2(self):
        # The row in the change that moves Alpha, or in a later one: either way Alpha comes back at S/f/alpha-2.
        for delayed in (False, True):
            with self.subTest(delayed=delayed), tempfile.TemporaryDirectory() as directory:
                repo = Repo(Path(directory) / "repo")
                c0 = repo.commit(START)
                row = move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")
                if delayed:
                    repo.commit(MOVED)
                    repo.commit(MOVED, [row])
                else:
                    repo.commit(MOVED, [row])
                repo.commit(START)
                record = repo.judge()
                self.assertEqual([(v.honoured, v.how) for v in record.verdicts], [(True, "recomputed")])
                self.assertEqual(record.live.get("S/f/alpha-2"), pages.Owner("topic", "Alpha", tuple(ALPHA)))
                self.assertNotIn("S/f/alpha", record.live)

    def test_a_topic_that_returns_takes_its_route_numbered(self):
        # A -> B -> A: Alpha is renamed, then renamed back, each move recorded; it returns at A-2, and the notice at A
        # follows B's row to A-2.
        repo = self.repo
        c0 = repo.commit(START)
        renamed = taxonomy({"f": [], "g": [], "h": []}, {"Alpha prime": ("S/f", ALPHA), "Beta": ("S/g", BETA)})
        c1 = repo.commit(renamed, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/f/alpha-prime")])
        repo.commit(START, [move("S/f/alpha-prime", c1, "topic", "Alpha prime", ALPHA, "S/f/alpha-2")])
        record = repo.judge()
        self.assertEqual([(v.honoured, v.how) for v in record.verdicts], [(True, "recomputed")] * 2)
        self.assertIn("S/f/alpha-2", record.live)
        notices, _ = record.notes
        self.assertEqual({route: (n.automatic, n.target) for route, n in notices.items()},
                         {"S/f/alpha": (True, "mathlib/S/f/alpha-2/index.html"),
                          "S/f/alpha-prime": (True, "mathlib/S/f/alpha-2/index.html")})

    def test_a_group_route_comes_back_under_its_title_and_keeps_another_scope_s_page_with_a_warning(self):
        repo = self.repo
        c0 = repo.commit(START)
        emptied = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/f", BETA)})
        repo.commit(emptied, [move("S/g", c0, "group", "Field g", BETA, "S/f")])
        record = repo.judge()
        self.assertEqual(record.notes[0]["S/g"], pages.Notice("S/g", "group", True, "mathlib/S/f/index.html",
                                                               "Field f"))
        self.assertIn("This section moved", pages.notice_page(record.notes[0]["S/g"]))
        # Back under the stored title: the page, no notice and no warning.
        repo.commit(START)
        record = repo.judge()
        self.assertIn("S/g", record.live)
        self.assertEqual(record.notes, ({}, []))
        # Another title holds the path: its page stays, with a warning.
        repo.commit(taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)},
                             titles={"g": "Field gamma"}))
        record = repo.judge()
        self.assertEqual(record.live["S/g"].title, "Field gamma")
        self.assertEqual(record.notes[0], {})
        self.assertEqual(len(record.notes[1]), 1)
        self.assertIn("keeps the page of the group 'Field gamma'", record.notes[1][0])
        self.assertIn("records the group 'Field g'", record.notes[1][0])

    def test_the_latest_group_row_by_first_parent_position_wins(self):
        # S/g retires, comes back, retires again. The second row's fragment sorts first by name: positions decide.
        repo = self.repo
        c0 = repo.commit(START)
        emptied = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/f", BETA)})
        repo.commit(emptied, [move("S/g", c0, "group", "Field g", BETA, "S/f")], stamp="20261101T000010Z")
        c2 = repo.commit(START)
        elsewhere = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/h", BETA)})
        repo.commit(elsewhere, [move("S/g", c2, "group", "Field g", BETA, "S/h")], stamp="20261101T000001Z")
        record = repo.judge()
        self.assertEqual([v.honoured for v in record.verdicts], [True, True])
        self.assertEqual(record.notes[0]["S/g"].target, "mathlib/S/h/index.html")
        self.assertTrue(record.notes[0]["S/g"].automatic)

    def test_two_group_rows_of_one_commit_give_a_plain_notice(self):
        repo = self.repo
        c0 = repo.commit(START)
        emptied = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/h", BETA)})
        repo.commit(emptied, [move("S/g", c0, "group", "Field g", BETA, "S/f"),
                              move("S/g", c0, "group", "Field g", BETA, "S/h")])
        record = repo.judge()
        self.assertEqual([v.honoured for v in record.verdicts], [True, True])
        notice = record.notes[0]["S/g"]
        self.assertEqual((notice.automatic, notice.target), (False, "mathlib/S/index.html"))
        self.assertIn("two rows at one commit", notice.reason)
        page = pages.notice_page(notice)
        self.assertIn("This section was reorganised", page)
        self.assertNotIn("location.replace", page)
        self.assertNotIn("refresh", page)

    def test_a_target_sharing_no_module_gives_a_plain_notice(self):
        # "Special": its modules leave the taxonomy, and its row sends it where none of them went.
        repo = self.repo
        tree = taxonomy({"f": [], "g": [], "h": []}, {"Special": ("S/f", GAMMA), "Beta": ("S/g", BETA)})
        c0 = repo.commit(tree)
        gone = taxonomy({"f": [], "g": [], "h": []}, {"Beta": ("S/g", BETA)}, excluded={m: "gone" for m in GAMMA})
        repo.commit(gone, [move("S/f/special", c0, "topic", "Special", GAMMA, "S/g/beta")])
        record = repo.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.honoured, verdict.plain), (True, True))
        notice = record.notes[0]["S/f/special"]
        self.assertEqual((notice.automatic, notice.target), (False, "mathlib/S/g/beta/index.html"))
        self.assertIn("This page was reorganised", pages.notice_page(notice))

    def test_a_field_that_becomes_a_subfield_redirects(self):
        repo = self.repo
        c0 = repo.commit(START)
        nested = taxonomy({"g": ["f"], "h": []}, {"Alpha": ("S/g/f", ALPHA), "Beta": ("S/g", BETA)},
                          titles={"g/f": "Field f"})
        repo.commit(nested, [move("S/f", c0, "group", "Field f", ALPHA, "S/g/f")])
        record = repo.judge()
        self.assertEqual(record.notes[0], {"S/f": pages.Notice("S/f", "group", True, "mathlib/S/g/f/index.html",
                                                               "Field f")})

    def test_a_pull_request_s_rows_are_refused_for_each_way_they_can_be_wrong(self):
        repo = self.repo
        c0 = repo.commit(START)
        repo.git("checkout", "-q", "-b", "side")
        side = repo.commit(START)
        repo.git("checkout", "-q", "main")
        base = repo.commit(MOVED)
        rows = [move("S/f/nothing", c0, "topic", "Nothing", ALPHA, "S/g/alpha"),
                move("S/f/alpha", side, "topic", "Alpha", ALPHA, "S/g/alpha"),
                move("S/f/alpha", "0" * 40, "topic", "Alpha", ALPHA, "S/g/alpha"),
                move("S/f", c0, "topic", "Field f", ALPHA, "S/g"),
                move("S/f/alpha", c0, "topic", "Alfa", ALPHA, "S/g/alpha"),
                move("S/f/alpha", c0, "group", "Alpha", ALPHA, "S/g/alpha"),
                move("S/f/alpha", c0, "topic", "Alpha", ALPHA[:1], "S/g/alpha")]
        expected = ["is no index page in the plan of", "is no commit of main's first-parent chain",
                    "is no commit of main's first-parent chain", "its kind differ", "its title differ",
                    "its kind differ", "its modules differ"]
        for row, reason in zip(rows, expected):
            with self.subTest(row=row):
                repo.clear()
                repo.write(MOVED, [row])
                record = repo.judge(base=base, strict=True)
                self.assertEqual([v.honoured for v in record.verdicts], [False])
                self.assertEqual(len(record.errors), 1, record.errors)
                self.assertIn(reason, record.errors[0])
        # A row whose commit has other universe inputs than the run's cannot be recomputed: a new one is refused.
        repo.clear()
        repo.files["lean-toolchain"] = "leanprover/lean4:v2\n"
        bumped = repo.commit(MOVED)
        repo.write(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        record = repo.judge(base=bumped, strict=True)
        self.assertEqual(len(record.errors), 1, record.errors)
        self.assertIn("cannot be recomputed", record.errors[0])
        self.assertIn("universe inputs", record.errors[0])
        # A malformed line is refused too.
        repo.clear()
        repo.write(MOVED, [{**move("S/f/../alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")}])
        record = repo.judge(base=bumped, strict=True)
        self.assertTrue(any("is no index route" in error for error in record.errors), record.errors)

    def test_after_a_pin_change_an_old_row_is_honoured_as_stored_and_groups_replay_its_title(self):
        repo = self.repo
        c0 = repo.commit(START)
        emptied = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/f", BETA)})
        repo.commit(emptied, [move("S/g", c0, "group", "Field g", BETA, "S/f")])
        repo.files["lake-manifest.json"] = manifest("2" * 40)
        repo.commit(emptied)
        record = repo.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.honoured, verdict.how), (True, "as stored"))
        self.assertIn("universe inputs", verdict.reason)
        self.assertTrue(record.notes[0]["S/g"].automatic)
        # The group's return is decided by the stored title alone.
        repo.commit(START)
        self.assertEqual(repo.judge().notes, ({}, []))
        repo.commit(taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)},
                             titles={"g": "Field gamma"}))
        notices, warnings = repo.judge().notes
        self.assertEqual(notices, {})
        self.assertEqual(len(warnings), 1)
        self.assertIn("records the group 'Field g'", warnings[0])

    def test_a_second_row_for_a_topic_route_is_refused_in_a_pull_request_and_plain_on_main(self):
        repo = self.repo
        c0 = repo.commit(START)
        base = repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        second = move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/beta")
        repo.write(MOVED, [second])
        record = repo.judge(base=base, strict=True)
        self.assertEqual(len(record.errors), 1, record.errors)
        self.assertIn("has a row already", record.errors[0])
        repo.git("add", "-A")
        repo.git("commit", "-q", "-m", "second")
        record = repo.judge()
        self.assertEqual([(v.honoured, v.duplicate) for v in record.verdicts], [(True, False), (True, True)])
        notice = record.notes[0]["S/f/alpha"]
        self.assertEqual((notice.automatic, notice.target), (False, "mathlib/S/index.html"))
        self.assertTrue(any("a second row" in warning for warning in record.warnings), record.warnings)

    def test_chains_end_at_a_live_page_and_never_at_a_notice(self):
        # Alpha is renamed (recorded), then its modules leave the taxonomy and its row sends it to Beta: the chain from
        # S/f/alpha reaches Beta's page, which shares no module with Alpha, so both notices are plain.
        repo = self.repo
        c0 = repo.commit(START)
        renamed = taxonomy({"f": [], "g": [], "h": []}, {"Alpha two": ("S/f", ALPHA), "Beta": ("S/g", BETA)})
        c1 = repo.commit(renamed, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/f/alpha-two")])
        gone = taxonomy({"f": [], "g": [], "h": []}, {"Beta": ("S/g", BETA)}, excluded={m: "gone" for m in ALPHA})
        repo.commit(gone, [move("S/f/alpha-two", c1, "topic", "Alpha two", ALPHA, "S/g/beta")])
        record = repo.judge()
        notices, _ = record.notes
        self.assertEqual({route: (n.automatic, n.target) for route, n in notices.items()},
                         {"S/f/alpha": (False, "mathlib/S/g/beta/index.html"),
                          "S/f/alpha-two": (False, "mathlib/S/g/beta/index.html")})
        routes = {pages.route_path(route) for route in notices}
        self.assertFalse(routes & {n.target for n in notices.values()})
        # A dead end: Alpha's row leads to S/g/alpha, which Alpha left again without a row.
        with tempfile.TemporaryDirectory() as directory:
            repo = Repo(Path(directory) / "dead")
            c0 = repo.commit(START)
            repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
            repo.commit(taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/h", ALPHA), "Beta": ("S/g", BETA)}))
            notices, warnings = repo.judge().notes
            self.assertEqual((notices["S/f/alpha"].automatic, notices["S/f/alpha"].target),
                             (False, "mathlib/S/g/index.html"))
            self.assertIn("neither live nor recorded", notices["S/f/alpha"].reason)
            self.assertEqual(len(warnings), 1)
        # A cycle: S/f retires to S/g, comes back, and S/g retires to S/f; then S/f retires without a row.
        with tempfile.TemporaryDirectory() as directory:
            repo = Repo(Path(directory) / "cycle")
            both = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)})
            c0 = repo.commit(both)
            only_g = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/g", ALPHA), "Beta": ("S/g", BETA)})
            c1 = repo.commit(only_g, [move("S/f", c0, "group", "Field f", ALPHA, "S/g")])
            only_f = taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/f", BETA)})
            repo.commit(only_f)
            repo.commit(only_f, [move("S/g", c1, "group", "Field g", ALPHA + BETA, "S/f")])
            repo.commit(taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/h", ALPHA), "Beta": ("S/h", BETA)}))
            record = repo.judge()
            self.assertEqual([v.honoured for v in record.verdicts], [True, True])
            notices, warnings = record.notes
            self.assertEqual({route: (n.automatic, n.target) for route, n in notices.items()},
                             {"S/f": (False, "mathlib/S/index.html"), "S/g": (False, "mathlib/S/index.html")})
            self.assertTrue(all("go round" in n.reason for n in notices.values()), notices)

    def test_a_fragment_is_judged_at_the_commit_of_main_that_introduces_it(self):
        # The row is right where it was introduced, by a merge: its target has moved on since, which a judgement
        # against today's taxonomy would refuse; main never judges it again so.
        repo = self.repo
        c0 = repo.commit(START)
        repo.git("checkout", "-q", "-b", "topic-branch")
        branch = repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        repo.git("checkout", "-q", "main")
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "topic-branch")
        merge = repo.git("rev-parse", "HEAD")
        repo.commit(taxonomy({"f": [], "g": [], "h": []}, {"Alpha": ("S/h", ALPHA), "Beta": ("S/g", BETA)}))
        record = repo.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.honoured, verdict.how, verdict.judged_at), (True, "recomputed", merge))
        self.assertNotEqual(verdict.judged_at, branch)
        self.assertEqual(verdict.position, 1)

    def test_a_refused_row_reserves_nothing_and_makes_no_duplicate(self):
        # Alpha still holds S/f/alpha, which ALPHA, with Beta's modules, held before. Two rows say S/f/alpha moved, one
        # for each witness: each is judged on its own and refused, in a pull request and on main alike, so neither
        # reserves the route nor makes the other a duplicate; Alpha keeps its page and nothing redirects.
        repo = self.repo
        c_earlier = repo.commit(taxonomy({"f": [], "g": []}, {"ALPHA": ("S/f", BETA), "First home": ("S/g", ALPHA)}))
        keep = taxonomy({"f": [], "g": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)})
        c = repo.commit(keep)
        repo.write(keep, [move("S/f/alpha", c, "topic", "Alpha", ALPHA, "S/g/beta"),
                          move("S/f/alpha", c_earlier, "topic", "ALPHA", BETA, "S/g/beta")])
        for strict in (True, False):
            with self.subTest(strict=strict):
                if not strict:
                    repo.git("add", "-A")
                    repo.git("commit", "-q", "-m", "rows")
                record = repo.judge(base=c, strict=True) if strict else repo.judge()
                complaints = record.errors if strict else record.warnings
                self.assertEqual([(v.honoured, v.duplicate) for v in record.verdicts], [(False, False)] * 2)
                self.assertEqual(len(complaints), 2, complaints)
                self.assertTrue(all("S/f/alpha is live at" in c and "it did not move" in c for c in complaints))
                self.assertEqual((record.reserved, record.live["S/f/alpha"]),
                                 (frozenset(), pages.Owner("topic", "Alpha", tuple(ALPHA))))
                self.assertEqual(record.notes, ({}, []))

    def test_a_returning_topic_takes_no_route_another_topic_keeps(self):
        # Alpha 2 has long held S/f/alpha-2. Alpha moves away, recorded, and comes back: S/f/alpha is reserved, and
        # S/f/alpha-2 is Alpha 2's natural route, so Alpha takes S/f/alpha-3 and Alpha 2 keeps its page.
        repo = self.repo
        existing = taxonomy({"f": [], "g": []}, {"Alpha": ("S/f", ALPHA), "Alpha 2": ("S/f", BETA)})
        c = repo.commit(existing)
        self.assertEqual({r: o.title for r, o in repo.judge().live.items() if r.startswith("S/f/")},
                         {"S/f/alpha": "Alpha", "S/f/alpha-2": "Alpha 2"})
        away = taxonomy({"f": [], "g": []}, {"Alpha": ("S/g", ALPHA), "Alpha 2": ("S/f", BETA)})
        c1 = repo.commit(away, [move("S/f/alpha", c, "topic", "Alpha", ALPHA, "S/g/alpha")])
        repo.commit(existing)
        record = repo.judge(base=c1, strict=True)
        self.assertEqual({r: o for r, o in record.live.items() if r.startswith("S/f/")},
                         {"S/f/alpha-2": pages.Owner("topic", "Alpha 2", tuple(BETA)),
                          "S/f/alpha-3": pages.Owner("topic", "Alpha", tuple(ALPHA))})
        self.assertFalse([line for line in record.advice("moves") if "changes owner" in line])

    def test_a_topic_never_takes_a_retired_group_s_route(self):
        # The subfield S/f/alpha retires, recorded. A new topic Alpha in f, unrelated, takes S/f/alpha-2, and the old
        # section's notice stays; the scope itself still comes back under its stored title, or keeps its page, with a
        # warning, under another.
        repo = self.repo
        old = taxonomy({"f": ["alpha"], "g": []}, {"Earlier": ("S/f/alpha", ALPHA), "Steady": ("S/g", GAMMA)},
                       titles={"f/alpha": "Ancient group"})
        c = repo.commit(old)
        gone = taxonomy({"f": [], "g": []}, {"Earlier": ("S/g", ALPHA), "Steady": ("S/g", GAMMA)})
        repo.commit(gone, [move("S/f/alpha", c, "group", "Ancient group", ALPHA, "S/g/earlier")])
        section = pages.Notice("S/f/alpha", "group", True, "mathlib/S/g/earlier/index.html", "Earlier")
        self.assertEqual(repo.judge().notes, ({"S/f/alpha": section}, []))
        repo.commit(taxonomy({"f": [], "g": []},
                             {"Earlier": ("S/g", ALPHA), "Steady": ("S/g", GAMMA), "Alpha": ("S/f", BETA)}))
        record = repo.judge()
        self.assertEqual(record.live.get("S/f/alpha-2"), pages.Owner("topic", "Alpha", tuple(BETA)))
        self.assertNotIn("S/f/alpha", record.live)
        self.assertEqual(record.notes, ({"S/f/alpha": section}, []))
        repo.commit(old)
        record = repo.judge()
        self.assertEqual((record.live["S/f/alpha"].title, record.notes), ("Ancient group", ({}, [])))
        repo.commit(taxonomy({"f": ["alpha"], "g": []}, {"Earlier": ("S/f/alpha", ALPHA), "Steady": ("S/g", GAMMA)},
                             titles={"f/alpha": "Replacement group"}))
        record = repo.judge()
        self.assertEqual((record.live["S/f/alpha"].title, record.notes[0]), ("Replacement group", {}))
        self.assertEqual(len(record.notes[1]), 1)
        self.assertIn("keeps the page of the group 'Replacement group'", record.notes[1][0])

    def test_a_split_chain_redirects_only_what_shares_the_final_page(self):
        # Alpha and Beta merge, recorded, and the merged topic keeps Alpha's modules alone, recorded: Alpha's and the
        # merged topic's notices redirect to the survivor, Beta's is plain.
        repo = self.repo
        c = repo.commit(taxonomy({"f": [], "g": []}, {"Alpha": ("S/f", ALPHA), "Beta": ("S/g", BETA)}))
        c1 = repo.commit(taxonomy({"f": [], "g": []}, {"Merged": ("S/g", ALPHA + BETA)}),
                         [move("S/f/alpha", c, "topic", "Alpha", ALPHA, "S/g/merged"),
                          move("S/g/beta", c, "topic", "Beta", BETA, "S/g/merged")])
        repo.commit(taxonomy({"f": [], "g": []}, {"Survivors": ("S/g", ALPHA)}),
                    [move("S/g/merged", c1, "topic", "Merged", ALPHA + BETA, "S/g/survivors")])
        notices, _ = repo.judge().notes
        survivors = "mathlib/S/g/survivors/index.html"
        self.assertEqual({route: (n.automatic, n.target) for route, n in notices.items()},
                         {"S/f/alpha": (True, survivors), "S/g/beta": (False, survivors),
                          "S/g/merged": (True, survivors)})

    def test_a_second_parent_commit_is_no_witness(self):
        # A commit reachable from main through a merge's second parent alone is not on main's first-parent chain.
        repo = self.repo
        c0 = repo.commit(START)
        repo.git("checkout", "-q", "-b", "side")
        side = repo.commit(START, [])
        repo.git("checkout", "-q", "main")
        repo.commit(MOVED)
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "side")
        base = repo.git("rev-parse", "HEAD")
        history = pages.History(repo.root, base, since=c0)
        self.assertEqual((history.at(c0), history.at(side)), (0, None))
        repo.write(MOVED, [move("S/f/alpha", side, "topic", "Alpha", ALPHA, "S/g/alpha")])
        record = repo.judge(base=base, strict=True)
        self.assertEqual(len(record.errors), 1, record.errors)
        self.assertIn("is no commit of main's first-parent chain", record.errors[0])

    def test_what_cannot_be_read_gives_main_no_authority(self):
        # Main's history cannot be established, or a witness lacks a universe input: nothing is proved, so the rows are
        # not honoured, never honoured as stored; only a proved change of universe inputs is (the pin change test).
        repo = self.repo
        c0 = repo.commit(START)
        repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        with mock.patch.object(pages, "PAGES_SINCE", "f" * 40):
            record = pages.MoveRecord(MODULES, checkout=repo.root)
        self.assertEqual([v.state for v in record.verdicts], ["unresolved"])
        self.assertTrue(any(warning.startswith("unresolved: ") for warning in record.warnings), record.warnings)
        self.assertTrue(record.prior_unresolved)
        with tempfile.TemporaryDirectory() as directory:
            other = Repo(Path(directory) / "absent")
            del other.files["scripts/extract_v2_lean_dependencies.py"]
            c0 = other.commit(START)
            v2 = "scripts/extract_v2_lean_dependencies.py"
            other.files[v2] = (ROOT / v2).read_bytes()
            other.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
            record = other.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.state, verdict.how), ("unresolved", ""))
        self.assertIn("cannot be verified", verdict.reason)
        self.assertIn("cannot all be read", verdict.reason)

    def test_a_fragment_edited_after_its_introduction_is_judged_as_introduced(self):
        # A row introduced with two of its owner's three modules is refused there; correcting the file later does not
        # make main honour the correction as if it had been introduced.
        repo = self.repo
        c0 = repo.commit(START)
        path = repo.fragment([move("S/f/alpha", c0, "topic", "Alpha", ALPHA[:1], "S/g/alpha")])
        introduced = repo.commit(MOVED)
        (repo.root / path).write_text(json.dumps(move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")) + "\n")
        repo.commit(MOVED)
        record = repo.judge()
        (verdict,) = record.verdicts
        self.assertEqual((verdict.honoured, verdict.judged_at, verdict.row.modules),
                         (False, introduced, tuple(ALPHA[:1])))
        self.assertIn("its modules differs", verdict.reason)
        changed = f"{path} changed after its introduction at {introduced[:12]}"
        self.assertTrue(any(changed in warning for warning in record.warnings), record.warnings)
        self.assertEqual(record.notes, ({}, []))

    def test_a_shallow_checkout_fetches_main_s_history_without_blobs(self):
        # As CI checks out a pull request's merge commit alone: the base by its id, then main's chain since
        # HISTORY_SINCE without blobs, then each blob it reads, all from `origin`.
        repo = self.repo
        c0 = repo.commit(START)
        base = repo.commit(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        repo.git("checkout", "-q", "-b", "pull")
        repo.commit(MOVED, [move("S/f", c0, "group", "Field f", ALPHA, "S/g")])
        repo.git("checkout", "-q", "-b", "merge", base)
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "pull")
        bare = repo.root.parent / "origin.git"
        subprocess.run(["git", "clone", "-q", "--bare", str(repo.root), str(bare)], check=True)
        for key in ("uploadpack.allowFilter", "uploadpack.allowAnySHA1InWant"):
            subprocess.run(["git", "-C", str(bare), "config", key, "true"], check=True)
        clone = repo.root.parent / "clone"
        subprocess.run(["git", "clone", "-q", "--depth=1", "--branch", "merge", f"file://{bare}", str(clone)],
                       check=True, capture_output=True)
        shallow = Repo.__new__(Repo)
        shallow.root = clone
        self.assertEqual(shallow.git("rev-parse", "--is-shallow-repository"), "true")
        with self.assertRaises(subprocess.CalledProcessError):
            shallow.git("cat-file", "-e", f"{base}^{{commit}}")
        with mock.patch.object(pages, "PAGES_SINCE", c0):
            record = pages.MoveRecord(MODULES, checkout=clone, base=base, strict=True)
        self.assertEqual(record.errors, [])
        self.assertEqual([(v.row.index, v.honoured, v.how, v.new) for v in record.verdicts],
                         [("S/f/alpha", True, "recomputed", False), ("S/f", True, "recomputed", True)])
        self.assertEqual(record.verdicts[0].judged_at, base)
        self.assertEqual(shallow.git("config", "remote.origin.promisor"), "true")

    def test_a_published_fragment_stays_as_it_is(self):
        repo = self.repo
        c0 = repo.commit(START)
        path = repo.write(MOVED, [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
        base = repo.commit(MOVED)
        file = repo.root / path
        original = file.read_bytes()
        file.write_bytes(original + b"\n")
        record = repo.judge(base=base, strict=True)
        self.assertTrue(any("changed; a published entry is never edited" in e for e in record.errors), record.errors)
        # Its mode is part of what stays.
        file.write_bytes(original)
        file.chmod(0o755)
        record = repo.judge(base=base, strict=True)
        self.assertTrue(any("changed; a published entry is never edited" in e for e in record.errors), record.errors)
        file.chmod(0o644)
        self.assertEqual(repo.judge(base=base, strict=True).errors, [])
        file.unlink()
        record = repo.judge(base=base, strict=True)
        self.assertTrue(any("is gone" in error for error in record.errors), record.errors)

    def test_the_helper_proposes_rows_traced_by_their_modules(self):
        repo = self.repo
        c0 = repo.commit(START)
        nested = taxonomy({"g": ["f"], "h": []}, {"Alpha": ("S/g/f", ALPHA), "Beta": ("S/g", BETA)},
                          titles={"g/f": "Field f"})
        repo.write(nested)
        record = repo.judge(base=c0)
        before = record.plan(record.snapshot(c0), frozenset())
        rows = pages.propose(before, record.live, record.module_set, c0)
        self.assertEqual(rows, [move("S/f", c0, "group", "Field f", ALPHA, "S/g/f"),
                                move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/f/alpha")])
        # The proposed rows pass the pull request's check as they are.
        repo.write(nested, rows)
        record = repo.judge(base=c0, strict=True)
        self.assertEqual((record.errors, [v.honoured for v in record.verdicts]), ([], [True, True]))
        self.assertEqual(sorted(record.notes[0]), ["S/f", "S/f/alpha"])
        self.assertTrue(all(n.automatic for n in record.notes[0].values()))
        # The advice names a vanished route without a row.
        repo.clear()
        repo.write(nested, rows[:1])
        record = repo.judge(base=c0, strict=True)
        advice = record.advice("moves --base X")
        self.assertTrue(any(line.startswith("advice: S/f/alpha, the topic 'Alpha', vanishes without a row")
                            for line in advice), advice)


class MoveFragmentTests(unittest.TestCase):
    def test_the_record_reads_its_folder_as_the_card_ledger_reads_its_own(self):
        # One corpus in both folders: the same fragments, in the same order, and the same refusals, their messages
        # equal up to the folder's name; and the writer's rules mirrored from scripts/card_moves.py are its own.
        self.assertEqual((pages.AHEAD, pages.STAMP, pages.SLUG.pattern),
                         (card_moves.AHEAD, card_moves.STAMP, card_moves.SLUG.pattern))
        row = json.dumps(move("S/f/alpha", "a" * 40, "topic", "Alpha", ALPHA, "S/g/alpha"))
        corpus = {
            "20260102T000000Z-b.jsonl": lambda p: p.write_text(row + "\n"),
            "20260101T000000Z-a.jsonl": lambda p: p.write_text("\n" + row + "\n\n" + row),
            "20260101T000000Z-a-2.jsonl": lambda p: p.write_text(row + "\n"),
            "notes.txt": lambda p: p.write_text(row),
            ".gitkeep": lambda p: p.write_text(""),
            "20260101T000000Z-Upper.jsonl": lambda p: p.write_text(row),
            "20260101T000000Z-x.json": lambda p: p.write_text(row),
            "20261301T000000Z-month.jsonl": lambda p: p.write_text(row),
            "20260101T250000Z-hour.jsonl": lambda p: p.write_text(row),
            "20260101T000000Z-link.jsonl": lambda p: p.symlink_to(p.parent.parent / "elsewhere.jsonl"),
            "20260101T000000Z-folder.jsonl": lambda p: p.mkdir(),
            "20260101T000000Z-empty.jsonl": lambda p: p.write_text(""),
            "20260101T000000Z-blank.jsonl": lambda p: p.write_text("\n  \n"),
            "20260101T000000Z-latin.jsonl": lambda p: p.write_bytes(b'{"index": "\xe9"}\n'),
            "2026010１T000000Z-wide.jsonl": lambda p: p.write_text(row),
            "20260101T000000Z-é.jsonl": lambda p: p.write_text(row),
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "elsewhere.jsonl").write_text(row)
            folders = {"card": root / "card-moves.d", "mathlib": root / "mathlib-moves.d"}
            for folder in folders.values():
                folder.mkdir()
                for name, make in corpus.items():
                    make(folder / name)

            def same(card, mine):
                cards, card_problems = card
                ours, our_problems = mine
                self.assertEqual([(p.replace(card_moves.FRAGMENTS, pages.MOVES), d) for p, d in cards], ours)
                self.assertEqual([p.replace(card_moves.FRAGMENTS, pages.MOVES) for p in card_problems], our_problems)

            card, mine = card_moves.read_fragments(folders["card"]), pages.read_move_fragments(folders["mathlib"])
            same(card, mine)
            self.assertEqual([path.rsplit("/", 1)[1] for path, _ in mine[0]],
                             ["20260101T000000Z-a-2.jsonl", "20260101T000000Z-a.jsonl", "20260102T000000Z-b.jsonl"])
            self.assertEqual(len(mine[1]), len(corpus) - 3)
            # A missing folder holds none; a file or a link in the folder's place is refused.
            for folder in folders.values():
                shutil.rmtree(folder)
            same(card_moves.read_fragments(folders["card"]), pages.read_move_fragments(folders["mathlib"]))
            self.assertEqual(pages.read_move_fragments(folders["mathlib"]), ([], []))
            for folder in folders.values():
                folder.write_text(row)
            same(card_moves.read_fragments(folders["card"]), pages.read_move_fragments(folders["mathlib"]))
            self.assertEqual(pages.read_move_fragments(folders["mathlib"])[1], ["scripts/mathlib-moves.d is no folder"])
            (root / "real").mkdir()
            (root / "real" / "20260101T000000Z-a.jsonl").write_text(row)
            for folder in folders.values():
                folder.unlink()
                folder.symlink_to(root / "real")
            same(card_moves.read_fragments(folders["card"]), pages.read_move_fragments(folders["mathlib"]))

    def test_the_writer_names_a_fragment_as_new_moves_does(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Repo(Path(directory) / "repo")
            c0 = repo.commit(START)
            rows = [move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")]
            repo.fragment(rows, stamp="20261126T120000Z")
            base = repo.commit(MOVED)
            now = datetime(2026, 11, 26, 12, 30, 0, 123, tzinfo=timezone.utc)
            folder = repo.root / pages.MOVES
            self.assertEqual(pages.write_moves(repo.root, "later", rows, base, now),
                             (0, f"{pages.MOVES}/20261126T123000Z-later.jsonl: 1 row"))
            self.assertEqual((folder / "20261126T123000Z-later.jsonl").read_text(), json.dumps(rows[0]) + "\n")
            # After a fragment stamped ahead of the clock, by up to an hour: one second after it.
            (folder / "20261126T131500Z-ahead.jsonl").write_text(json.dumps(rows[0]) + "\n")
            self.assertEqual(pages.write_moves(repo.root, "next", rows, base, now)[1],
                             f"{pages.MOVES}/20261126T131501Z-next.jsonl: 1 row")
            # More than an hour ahead: refused, saying when it would not be.
            (folder / "20261126T140000Z-far.jsonl").write_text(json.dumps(rows[0]) + "\n")
            status, message = pages.write_moves(repo.root, "late", rows, base, now)
            self.assertEqual(status, 1)
            self.assertIn("run again at 2026-11-26 13:00:01 UTC or later", message)
            # After the last stamp a name can have: refused, and waiting will not help.
            (folder / "99991231T235959Z-end.jsonl").write_text(json.dumps(rows[0]) + "\n")
            status, message = pages.write_moves(repo.root, "never", rows, base, now)
            self.assertEqual(status, 1)
            self.assertIn("waiting will not help", message)
            for name in ("20261126T140000Z-far.jsonl", "99991231T235959Z-end.jsonl"):
                (folder / name).unlink()
            # Never over a file or through a link: a name taken since it looked is refused.
            (folder / "20261126T131502Z-again.jsonl").symlink_to(repo.root / "lean-toolchain")
            with mock.patch.object(pages, "fresh_moves_name", lambda *_: ("20261126T131502Z-again.jsonl", None)):
                status, message = pages.write_moves(repo.root, "again", rows, base, now)
            self.assertEqual((status, message), (1, f"{pages.MOVES}/20261126T131502Z-again.jsonl is there already; "
                                                    "run again in a second"))
            self.assertEqual((repo.root / "lean-toolchain").read_text(), "leanprover/lean4:v1\n")
            (folder / "20261126T131502Z-again.jsonl").unlink()
            # A base it cannot read, or whose record is malformed, is refused.
            self.assertEqual(pages.write_moves(repo.root, "x", rows, "0" * 40, now)[0], 1)
            (folder / "notes.txt").write_text("x")
            repo.git("add", "-A")
            repo.git("commit", "-q", "-m", "malformed")
            status, message = pages.write_moves(repo.root, "x", rows, "HEAD", now)
            self.assertEqual(status, 1)
            self.assertIn("cannot be read in full", message)
            # No row, a bad slug, a linked folder: refused, nothing written.
            self.assertEqual(pages.write_moves(repo.root, "x", [], base, now)[0], 1)
            self.assertEqual(pages.write_moves(repo.root, "Bad", rows, base, now)[0], 2)
            shutil.move(str(folder), str(repo.root / "moved-away"))
            folder.symlink_to(repo.root / "moved-away")
            self.assertEqual(pages.write_moves(repo.root, "linked", rows, base, now),
                             (1, f"{pages.MOVES} is no folder"))

    def test_moves_writes_its_proposals_with_now_from_the_command_line(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Repo(Path(directory) / "repo")
            c0 = repo.commit(START)
            repo.write(MOVED)
            listing = Path(directory) / "modules.txt"
            listing.write_text("".join(f"{m}\n" for m in MODULES))
            printed = io.StringIO()
            with mock.patch.object(pages, "RECORD_ROOT", repo.root), mock.patch.object(pages, "PAGES_SINCE", c0), \
                    mock.patch.object(pages, "checkout_problem", lambda: None), \
                    contextlib.redirect_stdout(printed), contextlib.redirect_stderr(io.StringIO()):
                status = pages.main(["moves", "--base", c0, "--modules", str(listing), "--write", "alpha-moves",
                                     "--now", "20261126T120000Z"])
            self.assertEqual(status, 0, printed.getvalue())
            written = repo.root / pages.MOVES / "20261126T120000Z-alpha-moves.jsonl"
            self.assertEqual([json.loads(line) for line in written.read_text().splitlines()],
                             [move("S/f", c0, "group", "Field f", ALPHA, "S/g/alpha"),
                              move("S/f/alpha", c0, "topic", "Alpha", ALPHA, "S/g/alpha")])
            head = repo.commit(MOVED)
            # On a module list, the receipt is advisory, whatever its rows give: exit 3, never a pass of record.
            status, text = run_main(repo, c0, ["check-moves", "--base", c0, "--modules", str(listing)])
            self.assertEqual(status, pages.ADVISORY, text)
            self.assertIn("check-moves receipt: ADVISORY, NOT A VERIFICATION OF RECORD", text)
            self.assertIn("result: advisory, not a verification of record: 2 of 2 new rows pass on this list", text)
            self.assertNotIn("certified", text)
            # On a graph of a commit of main with the head's universe inputs: a verification of record, which names
            # the head, the base, the new fragment and the graph by their identities.
            graph = graph_inputs(Path(directory) / "graph", MODULES, c0)
            status, text = run_main(repo, c0, ["check-moves", "--base", c0, "--graph", str(graph)])
            self.assertEqual(status, pages.CERTIFIED, text)
            data = written.read_bytes()
            for line in ("check-moves receipt: verification of record",
                         f"head: {head} (its commit tree is judged; the working tree is not read)", f"base: {c0}",
                         f"  producer: ATLAS {c0} (main's first-parent chain, position 0)",
                         f"  modules with a node: 6, sorted list sha256 {pages.module_digest(MODULES)}",
                         f"  nodes.jsonl.gz sha256: {sha256(graph / 'nodes.jsonl.gz')}",
                         "new fragments: 1, 2 rows",
                         f"  {pages.MOVES}/20261126T120000Z-alpha-moves.jsonl: blob {pages.blob_id(data)}, sha256 "
                         f"{hashlib.sha256(data).hexdigest()}, 2 rows",
                         f"row {pages.MOVES}/20261126T120000Z-alpha-moves.jsonl:2: S/f/alpha -> S/g/alpha: honoured, "
                         "recomputed; its route at the head shows: automatic, to mathlib/S/g/alpha/index.html",
                         "result: certified: every one of the 2 new rows passes"):
                self.assertIn(line, text.splitlines())
            # The ZIP CI serves is read as the directory is, and its digest, the artifact's, is named.
            archive = Path(directory) / "graph.zip"
            with zipfile.ZipFile(archive, "w") as handle:
                for name in ("stats.json", "nodes.jsonl.gz"):
                    handle.write(graph / name, name)
            status, text = run_main(repo, c0, ["check-moves", "--base", c0, "--graph", str(archive)])
            self.assertEqual(status, pages.CERTIFIED, text)
            self.assertIn(f"graph: {archive}, a ZIP of sha256 {sha256(archive)}", text.splitlines())


class ReceiptTests(unittest.TestCase):
    """check-moves as a verification of record: on the head commit's tree, against a strict ancestor, on a graph whose
    provenance it establishes; and as an advisory check on a module list."""

    MODULES = ["Mathlib.A", "Mathlib.B", "Mathlib.C"]

    def sample(self, field: str) -> dict:
        return taxonomy({"f": [], "g": []}, {"Three modules": (f"S/{field}", self.MODULES)},
                        titles={"f": "Field F", "g": "Field G"})

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.work = Path(directory.name)
        self.repo = repo = Repo(self.work / "repo")
        self.c0 = repo.commit(self.sample("f"))
        repo.git("checkout", "-q", "-b", "side")
        repo.commit(self.sample("f"), [])
        repo.git("checkout", "-q", "main")
        repo.commit(self.sample("g"))
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "side")
        self.base = repo.git("rev-parse", "HEAD")
        # A row that claims two of the old topic's three modules.
        self.row = {**move("S/f/three-modules", self.c0, "topic", "Three modules", self.MODULES[:2],
                           "S/g/three-modules")}
        self.path = repo.fragment([self.row])
        self.head = repo.commit(self.sample("g"))
        self.full = graph_inputs(self.work / "graph", self.MODULES, self.head)

    def check_moves(self, *argv: str) -> tuple[int, str]:
        return run_main(self.repo, self.c0, ["check-moves", *argv])

    def test_the_real_graph_refuses_a_row_a_short_list_passes_only_as_advice(self):
        status, text = self.check_moves("--base", self.base, "--graph", str(self.full))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("its modules differs from its owner's", text)
        self.assertIn("result: refused: 1 of 1 new row do not pass", text.splitlines())
        short = self.work / "short.txt"
        short.write_text("Mathlib.A\nMathlib.B\n")
        status, text = self.check_moves("--base", self.base, "--modules", str(short))
        self.assertEqual(status, pages.ADVISORY, text)
        self.assertIn("result: advisory, not a verification of record: 1 of 1 new row pass on this list",
                      text.splitlines())
        self.assertNotIn("certified", text)

    def test_unknown_or_inconsistent_provenance_certifies_nothing(self):
        cases = {
            "unreadable": (graph_inputs(self.work / "unreadable", self.MODULES[:2], "e" * 40),
                           "the graph's producer commit eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee cannot be read here: "
                           "the graph's universe is unknown"),
            "pin": (graph_inputs(self.work / "pin", self.MODULES[:2], self.base, rev="2" * 40),
                    f"the graph's Mathlib pin {'2' * 40} is not the one its producer {self.base[:12]} pins, "
                    f"{'1' * 40}: the graph is inconsistent"),
            "nodeless": (graph_inputs(self.work / "nodeless", [], self.head), "the graph has no node"),
        }
        for name, (graph, reason) in cases.items():
            with self.subTest(name=name):
                status, text = self.check_moves("--base", self.base, "--graph", str(graph))
                self.assertEqual(status, pages.REFUSED, text)
                self.assertIn(f"not certified: {reason}", text.splitlines())
                self.assertIn("result: not certified", text.splitlines())
        # An unknown producer is no proved mismatch of pins.
        status, text = self.check_moves("--base", self.base, "--graph", str(cases["unreadable"][0]))
        self.assertNotIn("inconsistent", text)
        self.assertNotIn("other universe inputs", text)

    def test_a_receipt_judges_the_committed_head_against_a_strict_ancestor(self):
        status, text = self.check_moves("--base", self.head, "--graph", str(self.full))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("not certified: the base is the head: a receipt certifies what a head adds to its base",
                      text.splitlines())
        self.assertIn("not certified: the head adds no fragment to its base: there is nothing to certify",
                      text.splitlines())
        self.assertNotIn("result: certified", text)
        # A correction left uncommitted changes nothing: the commit's tree is judged.
        (self.repo.root / self.path).write_text(json.dumps({**self.row, "modules": self.MODULES}) + "\n")
        status, text = self.check_moves("--base", self.base, "--graph", str(self.full))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("its modules differs from its owner's", text)
        self.assertIn(f"head: {self.head} (its commit tree is judged; the working tree is not read)", text.splitlines())
        # Committed, the correction is certified.
        corrected = self.repo.commit(self.sample("g"))
        graph = graph_inputs(self.work / "corrected", self.MODULES, corrected)
        status, text = self.check_moves("--base", self.base, "--graph", str(graph))
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertIn(f"head: {corrected} (its commit tree is judged; the working tree is not read)", text.splitlines())
        self.assertIn(f"  producer: ATLAS {corrected} (the head)", text.splitlines())

    def test_an_unresolved_prior_row_certifies_nothing(self):
        # Main's record holds a row for the topic, witnessed at c0; a new row records it again, witnessed at c1, of the
        # same plan. With the whole history the new row is refused as a duplicate. When c0's taxonomy cannot be read,
        # the prior row is unresolved, which proves nothing: the new row is neither certified nor refused (exit 4) on
        # a pull request, and on main neither row gets any authority.
        repo = Repo(self.work / "prior")
        c0 = repo.commit(self.sample("f"))
        c1 = repo.commit({**self.sample("f"), "note": "a second witness of the same plan"})
        repo.commit(self.sample("g"))
        row = move("S/f/three-modules", c0, "topic", "Three modules", self.MODULES, "S/g/three-modules")
        intro = repo.commit(self.sample("g"), [row])
        candidate = repo.commit(self.sample("g"), [{**row, "existed_at": c1}])
        graph = graph_inputs(self.work / "prior-graph", self.MODULES, candidate)
        read = pages.History.read

        def unreadable(history, commit, path):
            if (commit, path) == (c0, pages.TAXONOMY_FILE):
                raise pages.Unavailable("the first witness's taxonomy cannot be read here")
            return read(history, commit, path)

        def check_moves() -> tuple[int, str]:
            return run_main(repo, c0, ["check-moves", "--base", intro, "--graph", str(graph)])

        status, text = check_moves()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("has a row already, and a recorded topic route is reserved for good", text)
        with mock.patch.object(pages.History, "read", unreadable):
            status, text = check_moves()
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn("result: not certified: prior record unresolved", text.splitlines())
        self.assertIn(f"not certified: prior record unresolved: {pages.MOVES}/20261101T000001Z-moves.jsonl:1: it "
                      "cannot be verified (the first witness's taxonomy cannot be read here): unresolved",
                      text.splitlines())
        self.assertIn("on what is known it passes", text)
        self.assertNotIn("result: certified", text)
        self.assertNotIn("result: refused", text)
        # Main's history unreadable altogether: unresolved as well.
        with mock.patch.object(pages.History, "introductions",
                               side_effect=pages.Unavailable("main's history cannot be read here")):
            status, text = check_moves()
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn("result: not certified: prior record unresolved", text.splitlines())
        # On main: with the whole history the first row is honoured and the second is a plain duplicate; without the
        # first witness neither is honoured or refused, nothing is reserved and no notice is written.
        with mock.patch.object(pages, "PAGES_SINCE", c0):
            whole = pages.MoveRecord(self.MODULES, checkout=repo.root, producer=candidate, pin="1" * 40)
            with mock.patch.object(pages.History, "read", unreadable):
                partial = pages.MoveRecord(self.MODULES, checkout=repo.root, producer=candidate, pin="1" * 40)
        self.assertEqual([(v.state, v.duplicate) for v in whole.verdicts], [("honoured", False), ("honoured", True)])
        self.assertEqual([v.state for v in partial.verdicts], ["unresolved", "unresolved"])
        self.assertEqual((partial.reserved, partial.errors, partial.prior_unresolved), (frozenset(), [], True))
        live = partial.plan(partial.head, partial.reserved)
        self.assertEqual(partial.notices(live, set(self.MODULES)), ({}, []))
        receipt = partial.receipt({}, [], live)
        self.assertEqual([entry["verdict"] for entry in receipt["rows"]], ["unresolved", "unresolved"])
        self.assertEqual(len(receipt["unresolved"]), 2)

    def test_a_pull_request_whose_record_alone_is_unresolved_is_neither_passed_nor_refused(self):
        unresolved = [f"{pages.NOT_CERTIFIED}prior record unresolved: main's history cannot be read here"]
        for errors, status in ((unresolved, pages.UNRESOLVED), (unresolved + ["a.html: changed"], pages.REFUSED),
                               ([], pages.CERTIFIED)):
            with self.subTest(errors=errors), mock.patch.object(pages, "check", lambda *_, **__: list(errors)), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(pages.main(["check", "site", "graph", "out"]), status)

    def test_a_graph_zip_holds_each_input_once(self):
        # ZipFile.read takes the last of two members of one name: a ZIP whose second nodes.jsonl.gz holds two of the
        # three modules would certify the row the whole inventory refuses. It is refused, and so are an alias of a
        # member, a missing member and a link. A ZIP laid out as CI's artifact, with the layer's other files, is read.
        full, short = graph_inputs(self.work / "zip-full", self.MODULES, self.base), \
            graph_inputs(self.work / "zip-short", self.MODULES[:2], self.base)
        link = zipfile.ZipInfo("nodes.jsonl.gz")
        link.external_attr = (stat.S_IFLNK | 0o777) << 16
        cases = {
            "two inventories": ([("stats.json", full / "stats.json"), ("nodes.jsonl.gz", full / "nodes.jsonl.gz"),
                                 ("nodes.jsonl.gz", short / "nodes.jsonl.gz")],
                                "the ZIP has 2 members at nodes.jsonl.gz, not one: its inventory would be ambiguous"),
            "an alias": ([("stats.json", full / "stats.json"), ("nodes.jsonl.gz", full / "nodes.jsonl.gz"),
                          ("./nodes.jsonl.gz", short / "nodes.jsonl.gz")], "the ZIP has 2 members at nodes.jsonl.gz"),
            "no stats.json": ([("nodes.jsonl.gz", short / "nodes.jsonl.gz")], "the ZIP has 0 members at stats.json"),
            "a link": ([("stats.json", full / "stats.json"), (link, b"elsewhere")],
                       "the ZIP's member 'nodes.jsonl.gz' is no regular file at nodes.jsonl.gz"),
        }
        for name, (members, reason) in cases.items():
            with self.subTest(name=name):
                archive = graph_zip(self.work / f"{name}.zip", members)
                status, text = self.check_moves("--base", self.base, "--graph", str(archive))
                self.assertEqual(status, pages.REFUSED, text)
                self.assertIn(reason, text)
                self.assertIn("result: not certified", text.splitlines())
        # The row corrected and committed: the CI-like ZIP certifies it.
        (self.repo.root / self.path).write_text(json.dumps({**self.row, "modules": self.MODULES}) + "\n")
        corrected = self.repo.commit(self.sample("g"))
        layer = graph_inputs(self.work / "zip-layer", self.MODULES, corrected)
        archive = graph_zip(self.work / "artifact.zip", [
            ("bridge-edges.jsonl.gz", gzip.compress(b"")), ("edges.jsonl.gz", gzip.compress(b"")),
            ("graph-meta.json", b"{}"), ("join-report.json", b"{}"), ("nodes.jsonl.gz", layer / "nodes.jsonl.gz"),
            ("SCHEMA.md", b"# The Mathlib layer\n"), ("stats.json", layer / "stats.json"),
            ("topics.jsonl.gz", gzip.compress(b""))])
        status, text = self.check_moves("--base", self.base, "--graph", str(archive))
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertIn(f"graph: {archive}, a ZIP of sha256 {sha256(archive)}", text.splitlines())

    def witnesses(self) -> tuple[Repo, str, str, str]:
        """The re-review's history: two witnesses of one plan (c0, c1), the topic moved, and a side branch merged
        (base), all on main's first-parent chain but the side commit."""
        repo = Repo(self.work / "witnesses")
        c0 = repo.commit({**self.sample("f"), "note": "first"})
        c1 = repo.commit({**self.sample("f"), "note": "second"})
        repo.git("checkout", "-q", "-b", "side")
        repo.commit({**self.sample("f"), "note": "second"}, [])
        repo.git("checkout", "-q", "main")
        repo.commit(self.sample("g"))
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "side")
        return repo, c0, c1, repo.git("rev-parse", "HEAD")

    def test_a_known_invalid_row_of_main_is_a_warning_and_a_new_one_an_error(self):
        # Main's record holds a row claiming two of the topic's three modules: refused where it was introduced, on all
        # its evidence, so it reserves nothing. A new row records the route rightly: certified, main's row a warning.
        repo, c0, c1, base = self.witnesses()
        wrong = move("S/f/three-modules", c0, "topic", "Three modules", self.MODULES[:2], "S/g/three-modules")
        bad = repo.commit(self.sample("g"), [wrong])
        right = {**wrong, "existed_at": c1, "modules": self.MODULES}
        graph = graph_inputs(self.work / "witness-graph", self.MODULES, base)
        old_row = f"{pages.MOVES}/20261101T000001Z-moves.jsonl:1"
        invalid = (f"{old_row}: its modules differs from its owner's in the plan of {c0[:12]}, the topic "
                   "'Three modules' with 3 modules")

        def check_moves() -> tuple[int, str]:
            return run_main(repo, c0, ["check-moves", "--base", bad, "--graph", str(graph)])

        repo.commit(self.sample("g"), [right])
        status, text = check_moves()
        lines = text.splitlines()
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertIn(f"warning: {invalid}", lines)
        self.assertIn("result: certified: every one of the 1 new row passes", lines)
        self.assertFalse([line for line in lines if line.startswith(("error:", "not certified:"))], text)
        # The pull request's gate reads the same record: no error.
        with mock.patch.object(pages, "PAGES_SINCE", c0):
            gate = pages.MoveRecord(self.MODULES, checkout=repo.root, base=bad, strict=True, producer=base,
                                    pin="1" * 40)
        self.assertEqual(([v.state for v in gate.verdicts], gate.errors, gate.unresolved),
                         (["refused", "honoured"], [], []))
        # Main's row unresolved instead, its witness unreadable: the new row is unresolved too (exit 4).
        read = pages.History.read

        def unreadable(history, commit, path):
            if (commit, path) == (c0, pages.TAXONOMY_FILE):
                raise pages.Unavailable("the first witness's taxonomy cannot be read here")
            return read(history, commit, path)

        with mock.patch.object(pages.History, "read", unreadable):
            status, text = check_moves()
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn("result: not certified: prior record unresolved", text.splitlines())
        # A new row as wrong as main's: refused, and the result counts it.
        repo.git("checkout", "-q", "-b", "fresh-invalid", bad)
        repo.commit(self.sample("g"), [{**wrong, "existed_at": c1}])
        status, text = check_moves()
        lines = text.splitlines()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(f"error: {pages.MOVES}/20261101T000003Z-moves.jsonl:1: its modules differs from its owner's "
                      f"in the plan of {c1[:12]}, the topic 'Three modules' with 3 modules", lines)
        self.assertIn(f"warning: {invalid}", lines)
        self.assertIn("result: refused: 1 of 1 new row do not pass", lines)
        # An error of the change beyond its rows, the published fragment edited, beside a right new row: the result
        # names it, never "0 of 1 new row do not pass".
        repo.git("checkout", "-q", "-b", "edited", bad)
        published = repo.root / f"{pages.MOVES}/20261101T000001Z-moves.jsonl"
        published.write_text(published.read_text() + "\n")
        repo.commit(self.sample("g"), [right])
        status, text = check_moves()
        lines = text.splitlines()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("result: refused: 1 error beyond the new rows", lines)
        self.assertFalse([line for line in lines if "0 of" in line], text)

    def test_an_unreadable_base_record_is_unresolved_never_an_empty_change(self):
        # A new right row, a compatible graph, readable head and base: certified. With only the base's fragment folder
        # unreadable, what the head adds is unknown, not nothing: exit 4. A definite error besides still refuses, and
        # a head that, read in full, adds nothing is refused.
        repo, c0, c1, base = self.witnesses()
        right = move("S/f/three-modules", c1, "topic", "Three modules", self.MODULES, "S/g/three-modules")
        clean = repo.commit(self.sample("g"), [right])
        graph = graph_inputs(self.work / "clean-graph", self.MODULES, base)
        fragments = pages.History.fragments

        def unreadable(history, commit):
            if commit == base:
                raise pages.Unavailable("the base's tree cannot be read here")
            return fragments(history, commit)

        def check_moves(since: str = base, graph_dir: Path = graph) -> tuple[int, str]:
            return run_main(repo, c0, ["check-moves", "--base", since, "--graph", str(graph_dir)])

        status, text = check_moves()
        self.assertEqual(status, pages.CERTIFIED, text)
        with mock.patch.object(pages.History, "fragments", unreadable):
            status, text = check_moves()
        lines = text.splitlines()
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn("new fragments: unknown, as main's record at the base cannot be read; the head's fragments hold "
                      "1 row", lines)
        self.assertIn(f"not certified: prior record unresolved: main's record at {base[:12]} cannot be read: the "
                      "base's tree cannot be read here", lines)
        self.assertIn("result: not certified: prior record unresolved", lines)
        self.assertNotIn("adds no fragment", text)
        with mock.patch.object(pages.History, "fragments", unreadable):
            status, text = check_moves(graph_dir=graph_inputs(self.work / "nodeless", [], base))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("not certified: the graph has no node", text.splitlines())
        # Whether the base is the head's ancestor, or the base itself, unreadable: unknown as well.
        with mock.patch.object(pages.History, "is_ancestor", lambda *_: None):
            status, text = check_moves()
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn(f"not certified: unresolved: whether the base {base[:12]} is an ancestor of the head cannot "
                      "be read here", text.splitlines())
        status, text = check_moves(since="f" * 40)
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn(f"not certified: unresolved: {'f' * 40} is no commit Git can read here", text.splitlines())
        self.assertNotIn("adds no fragment", text)
        # Read in full, a head that adds nothing to its base is refused.
        repo.commit(self.sample("g"))
        status, text = check_moves(since=clean)
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("not certified: the head adds no fragment to its base: there is nothing to certify",
                      text.splitlines())

    def test_a_path_of_main_s_record_is_never_a_new_fragment(self):
        # Main's record has an empty entry under a fragment's name. Filling that path edits a published entry: refused,
        # and no new fragment. The pull request's receipt and gate refuse it, and main, replaying the same head,
        # judges the path as introduced, empty: none reserves the route or writes a notice. The same row under a new
        # name, the empty entry unchanged, passes, with the reservation and the notice, in every mode.
        repo = Repo(self.work / "identity")
        a = repo.commit(START)
        repo.commit(MOVED)
        empty = repo.root / pages.MOVES / "20261101T000000Z-reserved-name.jsonl"
        empty.parent.mkdir(parents=True, exist_ok=True)
        empty.write_text("")
        repo.git("add", "-A")
        repo.git("commit", "-qm", "an empty entry on main")
        base = repo.git("rev-parse", "HEAD")
        graph = graph_inputs(self.work / "identity-graph", MODULES, base)
        data = json.dumps(move("S/f/alpha", a, "topic", "Alpha", ALPHA, "S/g/alpha")) + "\n"

        def outcome() -> tuple[int, str, list[pages.MoveRecord]]:
            head = repo.git("rev-parse", "HEAD")
            status, text = run_main(repo, a, ["check-moves", "--base", base, "--graph", str(graph)])
            with mock.patch.object(pages, "PAGES_SINCE", a):
                records = [pages.MoveRecord(MODULES, repo.root, base=base, strict=True, head=head, producer=base,
                                            pin="1" * 40),
                           pages.MoveRecord(MODULES, repo.root, base=base, strict=True, producer=base, pin="1" * 40),
                           pages.MoveRecord(MODULES, repo.root, head=head, producer=base, pin="1" * 40)]
            return status, text, records

        def shows(record: pages.MoveRecord) -> tuple[bool, bool]:
            live = record.plan(record.head, record.reserved)
            notices, _ = record.notices(live, record.module_set)
            return "S/f/alpha" in record.reserved, "S/f/alpha" in notices

        empty.write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "fill the old name")
        status, text, (receipt, gate, main) = outcome()
        edit = (f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl, an entry of main's record at {base[:12]}, "
                "changed; a published entry is never edited, even one that holds no fragment: put new rows in a new "
                "fragment")
        lines = text.splitlines()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(f"error: {edit}", lines)
        self.assertIn("new fragments: 0, 0 rows", lines)
        self.assertEqual((receipt.errors, gate.errors), ([edit], [edit]))
        self.assertEqual([shows(record) for record in (receipt, gate, main)], [(False, False)] * 3)
        self.assertEqual((main.verdicts, main.errors), ([], []))
        self.assertIn(f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl was introduced at {base[:12]} as no "
                      "fragment (no row; a fragment holds at least one): it introduced no row, and its later content "
                      "is not honoured", main.warnings)
        repo.git("checkout", "-q", "-b", "new-name", base)
        (empty.parent / "20261102T000000Z-distinct-new-name.jsonl").write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "a new name")
        status, text, records = outcome()
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertIn(f"warning: the record at {base[:12]}: {pages.MOVES}/20261101T000000Z-reserved-name.jsonl: no "
                      "row; a fragment holds at least one", text.splitlines())
        self.assertEqual([shows(record) for record in records], [(True, True)] * 3)
        self.assertEqual([record.errors for record in records], [[], [], []])
        # Removing the empty entry, or adding a malformed one, is the change's error as well.
        empty.unlink()
        (empty.parent / "notes.txt").write_text("a note")
        with mock.patch.object(pages, "PAGES_SINCE", a):
            gate = pages.MoveRecord(MODULES, repo.root, base=base, strict=True, producer=base, pin="1" * 40)
        self.assertTrue(any(error.startswith(f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl, an entry of "
                                             "main's record") and "is gone" in error for error in gate.errors),
                        gate.errors)
        self.assertTrue(any(error.startswith(f"{pages.MOVES}/notes.txt: ") for error in gate.errors), gate.errors)

    def test_a_working_tree_entry_has_git_s_identity(self):
        # The gate reads the working tree, the receipt Git's trees: both give an entry Git's mode, type and id.
        repo = Repo(self.work / "trees")
        folder = repo.root / pages.MOVES
        (folder / "a-folder.jsonl" / "inner").mkdir(parents=True)
        (folder / "a-folder.jsonl" / "inner" / "x").write_text("x")
        (folder / "a-folder.jsonl" / "y").write_bytes(b"y\n")
        (folder / "a-folder.jsonl" / "y").chmod(0o755)
        (folder / "a-link.jsonl").symlink_to("elsewhere")
        (folder / "20261101T000000Z-file.jsonl").write_text("{}\n")
        repo.git("add", "-A")
        repo.git("commit", "-qm", "entries")
        head = repo.git("rev-parse", "HEAD")
        committed = pages.History(repo.root, head).inventory(head)
        self.assertEqual(pages.scan_move_folder(folder, repo.root).entries, committed)
        # Read from the work tree itself, as for an entry the work tree changes, each is the same.
        self.assertEqual({f"{pages.MOVES}/{name}": pages.fs_identity(folder / name, "sha1")
                          for name in os.listdir(folder)}, committed)
        # A change in the work tree is read from the work tree.
        (folder / "a-folder.jsonl" / "y").write_bytes(b"z\n")
        changed = pages.scan_move_folder(folder, repo.root).entries
        self.assertNotEqual(changed[f"{pages.MOVES}/a-folder.jsonl"], committed[f"{pages.MOVES}/a-folder.jsonl"])
        self.assertEqual(changed[f"{pages.MOVES}/a-link.jsonl"], committed[f"{pages.MOVES}/a-link.jsonl"])

    def test_an_unreadable_copy_of_the_head_s_inputs_is_unknown_never_a_mismatch(self):
        # A right committed row, a readable producer and nothing else wrong: certified. Any one of the head's copies of
        # the scripts the receipt runs, unreadable here, leaves it unresolved (exit 4), never refused.
        (self.repo.root / self.path).write_text(json.dumps({**self.row, "modules": self.MODULES}) + "\n")
        head = self.repo.commit(self.sample("g"))
        graph = graph_inputs(self.work / "head-read-graph", self.MODULES, self.base)
        read = pages.History.read
        for target in (None, "scripts/card_moves.py", pages.PLANNER, "scripts/extract_mathlib_graph.py"):
            def unreadable(history, commit, path, target=target):
                if (commit, path) == (head, target):
                    raise pages.Unavailable("this head copy cannot be read here")
                return read(history, commit, path)

            with self.subTest(target=target), mock.patch.object(pages.History, "read", unreadable):
                status, text = self.check_moves("--base", self.base, "--graph", str(graph))
                lines = text.splitlines()
                if target is None:
                    self.assertEqual(status, pages.CERTIFIED, text)
                    continue
                self.assertEqual(status, pages.UNRESOLVED, text)
                self.assertIn(f"not certified: unresolved: the head's {target} cannot be read here (this head copy "
                              "cannot be read here)", lines)
                self.assertFalse([line for line in lines if line.startswith(("error:", "result: refused"))
                                  or line.startswith("not certified: ") and not line.startswith(
                                      ("not certified: unresolved: ", "not certified: prior record unresolved: "))],
                                 text)

    def modes(self, repo: Repo, since: str, base: str, graph: Path) -> tuple[int, str, list[pages.MoveRecord]]:
        """The receipt's exit and text for the checked-out head, and its record as the receipt, the pull request's gate
        on the working tree and main's replay of the same head judge it."""
        head = repo.git("rev-parse", "HEAD")
        status, text = run_main(repo, since, ["check-moves", "--base", base, "--graph", str(graph)])
        with mock.patch.object(pages, "PAGES_SINCE", since):
            records = [pages.MoveRecord(MODULES, repo.root, base=base, strict=True, head=head, producer=base,
                                        pin="1" * 40),
                       pages.MoveRecord(MODULES, repo.root, base=base, strict=True, producer=base, pin="1" * 40),
                       pages.MoveRecord(MODULES, repo.root, head=head, producer=base, pin="1" * 40)]
        return status, text, records

    @staticmethod
    def shows(record: pages.MoveRecord, route: str = "S/f/alpha") -> tuple[bool, bool]:
        """Whether ``record`` reserves ``route``, and writes a notice there."""
        live = record.plan(record.head, record.reserved)
        notices, _ = record.notices(live, record.module_set)
        return route in record.reserved, route in notices

    def occupied_path(self, first) -> tuple[Repo, str, str, str, Path]:
        """A history whose record folder has, at P, what ``first`` makes there, then the base; the row a candidate
        adds; and the graph."""
        repo = Repo(self.work / "occupied")
        a = repo.commit(START)
        repo.commit(MOVED)
        path = repo.root / pages.MOVES / "20261101T000000Z-reserved-name.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        first(repo, path)
        base = repo.git("rev-parse", "HEAD")
        data = json.dumps(move("S/f/alpha", a, "topic", "Alpha", ALPHA, "S/g/alpha")) + "\n"
        return repo, a, base, data, graph_inputs(self.work / "occupied-graph", MODULES, base)

    def test_a_name_main_s_record_once_had_is_never_new_again(self):
        # An empty file at P on main, removed before the base; the candidate adds a right row at P. P is no new
        # fragment: the receipt and the gate refuse it, and main, whose first entry at P is the empty file, honours
        # nothing there. A name never used passes in every mode.
        def empty_then_removed(repo: Repo, path: Path) -> None:
            path.write_text("")
            repo.git("add", "-A")
            repo.git("commit", "-qm", "an empty entry")
            path.unlink()
            repo.git("add", "-A")
            repo.git("commit", "-qm", "removed before the base")

        repo, a, base, data, graph = self.occupied_path(empty_then_removed)
        first = repo.git("rev-parse", "HEAD~1")
        path = repo.root / pages.MOVES / "20261101T000000Z-reserved-name.jsonl"
        path.write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "the old name again")
        status, text, (receipt, gate, main) = self.modes(repo, a, base, graph)
        reused = (f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl: main's record had this path at {first[:12]}, "
                  "a file, so it is no new fragment; a path main's record ever had is never used again, even once "
                  "removed: put new rows in a new fragment, under a new name")
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(f"error: {reused}", text.splitlines())
        self.assertEqual((receipt.errors, gate.errors, main.errors), ([reused], [reused], []))
        self.assertEqual([self.shows(record) for record in (receipt, gate, main)], [(False, False)] * 3)
        self.assertIn(f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl was introduced at {first[:12]} as no "
                      "fragment (no row; a fragment holds at least one): it introduced no row, and its later content "
                      "is not honoured", main.warnings)
        repo.git("checkout", "-q", "-b", "new-name", base)
        path.parent.mkdir(parents=True, exist_ok=True)
        (path.parent / "20261102T000000Z-distinct-new-name.jsonl").write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "a new name")
        status, text, records = self.modes(repo, a, base, graph)
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertEqual([self.shows(record) for record in records], [(True, True)] * 3)
        # Which paths main's record has had cannot be established: unresolved, and no authority on main.
        with mock.patch.object(pages.History, "introductions",
                               side_effect=pages.Unavailable("main's history cannot be read here")):
            status, text, (receipt, gate, main) = self.modes(repo, a, base, graph)
        self.assertEqual(status, pages.UNRESOLVED, text)
        self.assertIn("new fragments: unknown, as main's record at the base cannot be read; the head's fragments hold "
                      "1 row", text.splitlines())
        self.assertEqual([self.shows(record) for record in (receipt, gate, main)], [(False, False)] * 3)
        self.assertEqual([v.state for v in main.verdicts], ["unresolved"])

    def test_a_name_first_held_by_a_folder_never_introduces_a_row(self):
        # A folder, with a file in it, at P on main; the candidate makes P a right fragment. The receipt and the gate
        # refuse the edit, and main, whose first entry at P is the folder, honours nothing there. A name never used
        # passes in every mode.
        def folder(repo: Repo, path: Path) -> None:
            path.mkdir()
            (path / "note").write_text("a folder")
            repo.git("add", "-A")
            repo.git("commit", "-qm", "a folder at a fragment's name")

        repo, a, base, data, graph = self.occupied_path(folder)
        path = repo.root / pages.MOVES / "20261101T000000Z-reserved-name.jsonl"
        (path / "note").unlink()
        path.rmdir()
        path.write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "the folder made a fragment")
        status, text, (receipt, gate, main) = self.modes(repo, a, base, graph)
        self.assertEqual(status, pages.REFUSED, text)
        self.assertTrue(any(line.startswith(f"error: {pages.MOVES}/20261101T000000Z-reserved-name.jsonl, an entry of "
                                            "main's record") and "changed" in line for line in text.splitlines()), text)
        self.assertEqual([self.shows(record) for record in (receipt, gate, main)], [(False, False)] * 3)
        self.assertEqual((main.verdicts, main.errors), ([], []))
        self.assertIn(f"{pages.MOVES}/20261101T000000Z-reserved-name.jsonl was introduced at {base[:12]} as no "
                      "fragment (no regular file: a folder): it introduced no row, and its later content is not "
                      "honoured", main.warnings)
        repo.git("checkout", "-q", "-b", "new-name", base)
        (path.parent / "20261102T000000Z-distinct-new-name.jsonl").write_text(data)
        repo.git("add", "-A")
        repo.git("commit", "-qm", "a new name")
        status, text, records = self.modes(repo, a, base, graph)
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertEqual([self.shows(record) for record in records], [(True, True)] * 3)

    def test_where_each_path_is_first_occupied(self):
        # Every kind of entry occupies a path from its first commit on, whatever came after, merges read by their
        # first parent.
        repo = Repo(self.work / "occupancy")
        since = repo.commit(START)
        folder = repo.root / pages.MOVES
        folder.mkdir(parents=True)
        (folder / "a.jsonl").write_text("")
        (folder / "keep").write_text("")
        repo.git("add", "-A")
        repo.git("commit", "-qm", "a file")
        made_a = repo.git("rev-parse", "HEAD")
        (folder / "a.jsonl").unlink()
        (folder / "b.jsonl").mkdir()
        (folder / "b.jsonl" / "note").write_text("x")
        (folder / "c.jsonl").symlink_to("elsewhere")
        repo.git("add", "-A")
        repo.git("commit", "-qm", "a folder and a link")
        made_b = repo.git("rev-parse", "HEAD")
        (folder / "a.jsonl").write_text("{}\n")
        repo.git("checkout", "-q", "-b", "side")
        (folder / "a.jsonl").write_text("[]\n")
        (folder / "d.jsonl").write_text("{}\n")
        repo.git("add", "-A")
        repo.git("commit", "-qm", "side")
        repo.git("checkout", "-q", "main")
        repo.git("merge", "-q", "--no-ff", "-m", "merge", "side")
        merge = repo.git("rev-parse", "HEAD")
        with mock.patch.object(pages, "PAGES_SINCE", since):
            found = pages.History(repo.root, merge).introductions()
        kinds = {path.rsplit("/", 1)[1]: (commit, mode, kind) for path, (commit, (mode, kind, _)) in found.items()}
        self.assertEqual(kinds, {"a.jsonl": (made_a, "100644", "blob"), "keep": (made_a, "100644", "blob"),
                                 "b.jsonl": (made_b, "040000", "tree"), "c.jsonl": (made_b, "120000", "blob"),
                                 "d.jsonl": (merge, "100644", "blob")})

    def test_an_unchanged_submodule_entry_is_no_edit_in_a_fresh_clone(self):
        # Main's record holds a submodule entry, and the change adds only a right fragment under a new name. A clone
        # without submodules leaves the entry an empty folder; the gate reads it as the index has it, a commit, so the
        # receipt, the gate and main agree: the entry is a warning, the row honoured. Changing the entry, or making it
        # a fragment, is still an edit.
        repo = Repo(self.work / "gitlink")
        since = repo.commit(START)
        repo.commit(MOVED)
        library = Repo(self.work / "library")
        pinned, other = library.commit(START), library.commit(MOVED)
        old, new = f"{pages.MOVES}/20260101T000000Z-old.jsonl", f"{pages.MOVES}/20260102T000000Z-new.jsonl"
        (repo.root / ".gitmodules").write_text(f'[submodule "old"]\n\tpath = {old}\n\turl = ../library\n')
        repo.git("add", ".gitmodules")
        repo.git("update-index", "--add", "--cacheinfo", f"160000,{pinned},{old}")
        repo.git("commit", "-qm", "a submodule entry in the record")
        base = repo.git("rev-parse", "HEAD")
        (repo.root / new).parent.mkdir(parents=True, exist_ok=True)
        (repo.root / new).write_text(json.dumps(move("S/f/alpha", since, "topic", "Alpha", ALPHA, "S/g/alpha")) + "\n")
        repo.git("add", "--", new)
        repo.git("commit", "-qm", "a new fragment")
        graph = graph_inputs(self.work / "gitlink-graph", MODULES, base)
        clones = iter(range(10))

        def outcome() -> tuple[int, str, list[pages.MoveRecord], Path]:
            head = repo.git("rev-parse", "HEAD")
            status, text = run_main(repo, since, ["check-moves", "--base", base, "--graph", str(graph)])
            clone = self.work / f"clone-{next(clones)}"
            subprocess.run(["git", "clone", "-q", "--no-recurse-submodules", str(repo.root), str(clone)], check=True)
            with mock.patch.object(pages, "PAGES_SINCE", since):
                records = [pages.MoveRecord(MODULES, clone, base=base, strict=True, head=head, producer=base,
                                            pin="1" * 40),
                           pages.MoveRecord(MODULES, clone, base=base, strict=True, producer=base, pin="1" * 40),
                           pages.MoveRecord(MODULES, clone, head=head, producer=base, pin="1" * 40)]
            return status, text, records, clone

        status, text, records, clone = outcome()
        self.assertTrue((clone / old).is_dir() and not any((clone / old).iterdir()))
        self.assertEqual(pages.scan_move_folder(clone / pages.MOVES, clone).entries[old], ("160000", "commit", pinned))
        self.assertEqual(status, pages.CERTIFIED, text)
        self.assertIn(f"warning: the record at {base[:12]}: {old}: no regular file", text.splitlines())
        self.assertEqual([record.errors for record in records], [[], [], []])
        self.assertEqual([self.shows(record) for record in records], [(True, True)] * 3)
        # The entry pinned to another commit: an edit, in the receipt and the gate.
        repo.git("update-index", "--cacheinfo", f"160000,{other},{old}")
        repo.git("commit", "-qm", "the submodule entry moved")
        edit = (f"{old}, an entry of main's record at {base[:12]}, changed; a published entry is never edited, even "
                "one that holds no fragment: put new rows in a new fragment")
        status, text, (receipt, gate, _), _ = outcome()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(edit, receipt.errors)
        self.assertIn(edit, gate.errors)
        # The entry made a fragment: an edit as well.
        repo.git("reset", "-q", "--hard", "HEAD~1")
        repo.git("rm", "-q", "--cached", old)
        if (repo.root / old).is_dir():
            (repo.root / old).rmdir()  # the empty folder Git leaves for the entry
        (repo.root / old).parent.mkdir(parents=True, exist_ok=True)
        (repo.root / old).write_text(json.dumps(move("S/f/alpha", since, "topic", "Alpha", ALPHA, "S/g/alpha")) + "\n")
        repo.git("add", "--", old)
        repo.git("commit", "-qm", "the submodule entry made a fragment")
        status, text, (receipt, gate, _), _ = outcome()
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(edit, receipt.errors)
        self.assertIn(edit, gate.errors)

    def test_a_graph_of_another_universe_or_a_change_of_universe_inputs(self):
        # The v2 extractor changes: a new row whose commit has the old inputs cannot be recomputed and is refused, and
        # a graph of the old inputs cannot stand for the head's plans.
        repo = self.repo
        repo.files["scripts/extract_v2_lean_dependencies.py"] = "# v2, second version\n"
        bumped = repo.commit(self.sample("g"))
        repo.fragment([move("S/f", self.c0, "group", "Field F", self.MODULES, "S/g")])
        head = repo.commit(self.sample("g"))
        status, text = self.check_moves("--base", bumped, "--graph",
                                        str(graph_inputs(self.work / "new", self.MODULES, head)))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn("it cannot be recomputed (the universe inputs of", text)
        self.assertIn("are not the run's (scripts/extract_v2_lean_dependencies.py)), and a new row must be", text)
        status, text = self.check_moves("--base", bumped, "--graph", str(self.full))
        self.assertEqual(status, pages.REFUSED, text)
        self.assertIn(f"not certified: the graph's producer {self.head[:12]} has other universe inputs than the head "
                      "(scripts/extract_v2_lean_dependencies.py): the graph cannot stand for the head's plans",
                      text.splitlines())
        # On main, the published row of the old inputs is honoured as stored, the change being proved.
        with mock.patch.object(pages, "PAGES_SINCE", self.c0):
            record = pages.MoveRecord(self.MODULES, checkout=repo.root)
        first = next(v for v in record.verdicts if v.row.path == self.path)
        self.assertEqual((first.honoured, first.how), (True, "as stored"))
        self.assertIn("are not the run's (scripts/extract_v2_lean_dependencies.py)", first.reason)


# The fixture site's topic once had another title, and a field once held the old module.
EARLIER = {"subjects": {"NumberTheory": {"title": "Number theory", "description": "", "fields": [
    {"slug": "diophantine-equations", "title": "Diophantine equations", "description": ""},
    {"slug": "elliptic", "title": "Elliptic", "description": ""}]}},
    "placements": {"Mathlib/Foo/Basic": {"to": TOPIC, "title": "Old fixture topic"},
                   "Mathlib/Baz": {"to": TOPIC, "title": "Old fixture topic"},
                   "Mathlib/Old": {"to": "NumberTheory/elliptic", "title": "Elliptic things"}}}
LATER = {**EARLIER, "placements": {"Mathlib/Foo/Basic": {"to": TOPIC, "title": "Fixture topic"},
                                   "Mathlib/Baz": {"to": TOPIC, "title": "Fixture topic"}},
         "mathlib_exclusions": {"Mathlib/Old": "an old module"}}
OLD_TOPIC = f"{TOPIC}/old-fixture-topic"


class MoveNoticeSiteTests(unittest.TestCase):
    """The notices of a record in the built site: written, checked both ways, and packed for GitHub Pages."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        root = Path(cls.directory.name)
        cls.graph, cls.site = make_graph(root), make_site(root)
        cls.repo = Repo(root / "record")
        cls.repo.files["lake-manifest.json"] = manifest(REV)
        c0 = cls.repo.commit(EARLIER)
        cls.repo.commit(LATER)
        cls.head = cls.repo.commit(LATER, [
            move(OLD_TOPIC, c0, "topic", "Old fixture topic", ["Mathlib.Baz", "Mathlib.Foo.Basic"],
                 f"{TOPIC}/fixture-topic"),
            move("NumberTheory/elliptic", c0, "group", "Elliptic", ["Mathlib.Old"], "NumberTheory")])
        stamp(cls.graph, cls.site, cls.head)
        cls.patches = [mock.patch.object(pages, "TAXONOMY", cls.repo.root / "scripts" / "taxonomy.json"),
                       mock.patch.object(pages, "PAGES_SINCE", c0),
                       mock.patch.object(pages, "RECORD_ROOT", cls.repo.root)]
        for patch in cls.patches:
            patch.start()
        cls.out, cls.bare = root / "out", root / "bare"
        cls.report = quiet_build(cls.site, cls.graph, cls.out, MKDOCS)
        quiet_build(cls.site, cls.graph, cls.bare, MKDOCS, record=root / "no-record")

    @classmethod
    def tearDownClass(cls):
        for patch in cls.patches:
            patch.stop()
        cls.directory.cleanup()

    def tampered(self, edit) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory) / "out"
            shutil.copytree(self.out, copy)
            edit(copy)
            return pages.check(self.site, self.graph, copy)

    def test_the_build_writes_a_notice_at_each_honoured_route_no_page_holds(self):
        moves = self.report["moves"]
        # What a receipt says a route shows is read from the notices the build writes.
        self.assertEqual([(row["verdict"], row["how"], row["route_shows"]) for row in moves["rows"]],
                         [("honoured", "recomputed", f"automatic, to mathlib/{TOPIC}/fixture-topic/index.html"),
                          ("honoured", "recomputed", "plain, to mathlib/NumberTheory/index.html")])
        graph = moves["graph"]
        self.assertEqual((moves["head"], graph["producer"], graph["trust"], graph["modules"]),
                         (self.head, self.head, "this run's own artifact", 3))
        self.assertEqual([(n["index"], n["notice"], n["to"]) for n in moves["notices"]],
                         [(OLD_TOPIC, "automatic", f"mathlib/{TOPIC}/fixture-topic/index.html"),
                          ("NumberTheory/elliptic", "plain", "mathlib/NumberTheory/index.html")])
        self.assertEqual(self.report["mathlib_notices"], 2)
        automatic = (self.out / pages.route_path(OLD_TOPIC)).read_text()
        self.assertIn("<title>This page moved - ATLAS</title>", automatic)
        self.assertIn('<a href="../fixture-topic/index.html">Continue to Fixture topic</a>', automatic)
        self.assertIn('<link rel="canonical" href="../fixture-topic/index.html">', automatic)
        self.assertIn('<noscript><meta http-equiv="refresh" content="0; url=../fixture-topic/index.html"></noscript>',
                      automatic)
        self.assertIn('new URL("../fixture-topic/index.html",location.href);if(!to.hash)to.hash=location.hash;'
                      "location.replace(to.href)", automatic)
        self.assertIn('<meta name="robots" content="noindex">', automatic)
        plain = (self.out / "mathlib/NumberTheory/elliptic/index.html").read_text()
        self.assertIn("<h1>This section was reorganised</h1>", plain)
        self.assertIn('<a href="../index.html">Continue to Number theory</a>', plain)
        for absent in ("location.replace", "refresh", "canonical"):
            self.assertNotIn(absent, plain)
        # Out of search, out of the navigation and the counts: the build without the record differs by the notices
        # alone.
        search = json.loads((self.out / pages.SEARCH_INDEX).read_text())
        self.assertFalse([doc for doc in search["docs"] if "elliptic" in doc["location"] or "old-fixture" in
                          doc["location"]])
        files = {p.relative_to(self.out).as_posix() for p in self.out.rglob("*") if p.is_file()}
        bare = {p.relative_to(self.bare).as_posix() for p in self.bare.rglob("*") if p.is_file()}
        self.assertEqual(files - bare, {pages.route_path(OLD_TOPIC), "mathlib/NumberTheory/elliptic/index.html"})
        self.assertEqual(bare - files, set())
        self.assertEqual([p for p in bare if (self.out / p).read_bytes() != (self.bare / p).read_bytes()], [])

    def test_check_takes_the_notices_both_ways(self):
        self.assertEqual(pages.check(self.site, self.graph, self.out), [])
        notice = pages.route_path(OLD_TOPIC)

        def missing(copy):
            (copy / notice).unlink()

        def stray(copy):
            (copy / "mathlib/NumberTheory/stray").mkdir(parents=True)
            shutil.copy(copy / notice, copy / "mathlib/NumberTheory/stray/index.html")

        def disagreeing(copy):
            page = copy / notice
            page.write_text(page.read_text().replace('new URL("../fixture-topic/index.html"',
                                                     'new URL("../index.html"'))

        def searched(copy):
            index = copy / pages.SEARCH_INDEX
            search = json.loads(index.read_text())
            search["docs"].append({"location": notice, "text": "", "title": "This page moved"})
            index.write_text(json.dumps(search))

        errors = self.tampered(missing)
        self.assertTrue(any(e.startswith(f"{notice}: missing") for e in errors), errors)
        errors = self.tampered(stray)
        self.assertTrue(any("stray/index.html: a notice that no honoured row" in e for e in errors), errors)
        errors = self.tampered(disagreeing)
        self.assertTrue(any(e == f"{notice}: not the notice its honoured row gives" for e in errors), errors)
        self.assertTrue(any(e.startswith(f"{notice}: its script is ['../index.html']") for e in errors), errors)
        errors = self.tampered(searched)
        self.assertTrue(any("is a notice, which stays out of search" in e for e in errors), errors)

    def test_a_pull_request_s_check_takes_only_its_own_run_s_graph(self):
        # CI's same-run artifact: its producer is the checkout's HEAD. A graph of another commit is refused there,
        # whatever it holds.
        with tempfile.TemporaryDirectory() as directory:
            graph = Path(directory) / "graph"
            shutil.copytree(self.graph, graph)
            stats = json.loads((graph / "stats.json").read_text())
            stats["versions"]["atlas_commit"] = "c" * 40
            (graph / "stats.json").write_text(json.dumps(stats))
            errors = pages.check(self.site, graph, self.out, pull_request=self.head)
        self.assertTrue(any("not of this checkout's HEAD" in error for error in errors), errors)
        # Its universe unknown, the record is unresolved, on lines of their own; the wrong producer is an error.
        self.assertTrue(any(error.startswith(f"{pages.NOT_CERTIFIED}prior record unresolved: the graph's producer "
                                             "commit cccccccccccc") for error in errors), errors)
        # Nothing is honoured on a graph of unknown universe, so the notices the build wrote have no row behind them.
        self.assertTrue(any("a notice that no honoured row" in error for error in errors), errors)
        self.assertEqual(pages.check(self.site, self.graph, self.out), [])

    def test_both_route_forms_lead_to_the_live_page_from_every_prefix(self):
        self.assertEqual(len(self.report["moves"]["notices"]), 2)
        for prefix in ("file:///srv/site-full/", "https://facebookresearch.github.io/atlas-lean/",
                       "https://mirror.example/share/a/0123/site/"):
            for notice in self.report["moves"]["notices"]:
                page = (self.out / notice["path"]).read_text()
                href = html.unescape(pages.NOTICE_LINK.search(page).group(1))
                folder = prefix + notice["path"][: -len("index.html")]
                with self.subTest(prefix=prefix, notice=notice["index"]):
                    self.assertEqual(urljoin(folder, href), urljoin(folder + "index.html", href))
                    self.assertEqual(urljoin(folder, href), prefix + notice["to"])
                    self.assertTrue((self.out / notice["to"]).is_file())
                    self.assertNotIn(notice["to"], [n["path"] for n in self.report["moves"]["notices"]])

    def test_the_github_pages_copy_packs_the_notices_like_any_page(self):
        self.assertEqual(len(self.report["moves"]["notices"]), 2)
        with tempfile.TemporaryDirectory() as directory:
            packed, bare = Path(directory) / "packed", Path(directory) / "bare"
            pack_pages_site.pack(self.out, packed)
            pack_pages_site.pack(self.bare, bare)
            self.assertEqual(pack_pages_site.check(self.out, packed), [])
            for notice in self.report["moves"]["notices"]:
                served = (packed / notice["path"]).read_bytes()
                # The served page is the generic small page: no link, no redirect; the stored page is the notice.
                for absent in (b"<a ", b"refresh", b"canonical", b"location.replace"):
                    self.assertNotIn(absent, served)
                self.assertEqual(gzip.decompress((packed / (notice["path"] + ".gz")).read_bytes()),
                                 (self.out / notice["path"]).read_bytes())
                self.assertTrue((packed / notice["to"]).is_file() and (packed / (notice["to"] + ".gz")).is_file())
            files = {p.relative_to(packed).as_posix(): p.stat().st_size for p in packed.rglob("*") if p.is_file()}
            before = {p.relative_to(bare).as_posix(): p.stat().st_size for p in bare.rglob("*") if p.is_file()}
            added = sorted(set(files) - set(before))
            self.assertEqual(added, sorted(f"{n['path']}{gz}" for n in self.report["moves"]["notices"]
                                           for gz in ("", ".gz")))
            self.assertEqual(sum(files[p] for p in added), sum(files.values()) - sum(before.values()))


if __name__ == "__main__":
    unittest.main()
