#!/usr/bin/env python3
"""Tests for scripts/build_mathlib_pages.py and scripts/mathlib_link.py on a small site and Mathlib layer."""

from __future__ import annotations

import contextlib
import gzip
import html
import io
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from html.parser import HTMLParser
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_mathlib_pages as pages  # noqa: E402
import mathlib_link  # noqa: E402

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
        cls.graph, cls.site, cls.out = make_graph(root), make_site(root), root / "out"
        cls.report = quiet_build(cls.site, cls.graph, cls.out, MKDOCS)

    @classmethod
    def tearDownClass(cls):
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


if __name__ == "__main__":
    unittest.main()
