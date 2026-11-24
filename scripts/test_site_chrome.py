"""Regressions for the published site's page chrome: hooks/trim_pages.py and theme/partials/nav.html."""

from __future__ import annotations

import importlib.util
import logging
import posixpath
import tempfile
import types
import unittest
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load_hook(name: str) -> types.ModuleType:
    """Import hooks/<name>.py, which MkDocs loads by path rather than as a package module."""

    spec = importlib.util.spec_from_file_location(f"atlas_hook_{name}", ROOT / "hooks" / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


trim_pages = load_hook("trim_pages")


class CompactTests(unittest.TestCase):
    def assertKept(self, page: str) -> None:
        self.assertEqual(trim_pages.compact(page), page)

    def test_indentation_between_tags_becomes_one_line_break(self) -> None:
        page = "<ul>\n      <li>\n        <a href=\"a.html\">A</a>\n      </li>\n    \n</ul>\n"
        self.assertEqual(trim_pages.compact(page), "<ul>\n<li>\n<a href=\"a.html\">A</a>\n</li>\n</ul>\n")

    def test_runs_without_a_line_break_and_no_break_spaces_are_kept(self) -> None:
        self.assertKept("<p>a   b</p>")
        self.assertEqual(trim_pages.compact("<p>a\n  \u00a0 b</p>"), "<p>a\n\u00a0 b</p>")

    def test_verbatim_elements_keep_their_whitespace(self) -> None:
        for element in (
            "<pre class=\"bp-lean\"><code>theorem t :\n    True := by\n  trivial</code></pre>",
            "<code>a\n   b</code>",
            "<kbd>Ctrl\n   C</kbd>",
            "<textarea>\n  kept <b>\n  </textarea>",
            "<script>var x = 1;\n    var y = \"<div>\";</script>",
            "<style>\n  .a { color: red; }\n</style>",
            "<title>A\n   B</title>",
            "<noscript>\n  <p>x</p>\n</noscript>",
            "<div class=\"bp-review bp-as-typed\">line\n    indented</div>",
            "<span class='bp-readback-body'>a\n  b</span>",
            "<span class=\"arithmatex\">\\(a\n   \\\\\n   b\\)</span>",
            "<div class=\"arithmatex\">\\[\n  x\n\n  y\n\\]</div>",
            "<div class=\"mermaid\">mindmap\n  root\n    child\n      grandchild\n    sibling</div>",
        ):
            with self.subTest(element=element):
                self.assertEqual(trim_pages.compact(f"<div>\n  {element}\n  </div>"), f"<div>\n{element}\n</div>")

    def test_tags_comments_and_attribute_values_are_kept(self) -> None:
        self.assertKept("<input value=\"a\n    b\">")
        self.assertKept("<p title='x\n   y'\n     class=\"c\">z</p>")
        self.assertKept("<!--\n   a\n   -->")
        self.assertKept("<pre>a<!-- </pre> -->\n    b</pre>")
        self.assertKept("<!doctype html>")

    def test_a_quoted_angle_bracket_does_not_hide_a_verbatim_class(self) -> None:
        self.assertKept("<div title=\"a > b\" class=\"bp-as-typed\">x\n   y</div>")

    def test_classes_are_read_from_the_class_attribute_only(self) -> None:
        self.assertKept("<div title=\"example class=ordinary\" class=\"bp-as-typed\">a\n    b</div>")
        self.assertKept("<div class=\"bp-as&#45;typed\">a\n    b</div>")
        self.assertKept("<div class=bp-as-typed>a\n    b</div>")
        self.assertEqual(
            trim_pages.compact("<div title=\"class=bp-as-typed\">a\n    b</div>"),
            "<div title=\"class=bp-as-typed\">a\nb</div>",
        )
        # A no-break space is not HTML whitespace, so it does not separate classes.
        self.assertEqual(
            trim_pages.compact("<div class=\"x\u00a0bp-as-typed\">a\n    b</div>"),
            "<div class=\"x\u00a0bp-as-typed\">a\nb</div>",
        )

    def test_a_no_break_space_does_not_end_a_closing_tag_name(self) -> None:
        self.assertKept("<textarea>a</textarea\u00a0>\n    b</textarea>")
        self.assertKept("<script>var t = `a</script\u00a0>\n    b`;</script>")

    def test_tag_names_ignore_the_case_of_ascii_letters_only(self) -> None:
        # Unicode case folding would read U+0131 as `i` and U+017F as `s`; HTML does not.
        self.assertKept("<div><script>m=\"</scr\u0131pt>\";d=\"</div>\";v=`a\n    b`;</script></div>")
        self.assertKept("<div><style>p::after { content: '</\u017ftyle></div>'; }\n    </style></div>")
        self.assertKept("<SCRIPT>var x = 1;\n    var y = 2;</Script>")

    def test_nested_elements_close_at_their_own_end(self) -> None:
        page = "<pre>a\n  <pre>b\n  </pre>\n  c</pre>\n   <p>\n   d</p>"
        self.assertEqual(trim_pages.compact(page), "<pre>a\n  <pre>b\n  </pre>\n  c</pre>\n<p>\nd</p>")

    def test_a_closing_tag_closes_the_verbatim_elements_left_open_inside(self) -> None:
        self.assertEqual(trim_pages.compact("<div><code>a\n  b</div>\n   c"), "<div><code>a\n  b</div>\nc")

    def test_raw_text_ends_at_its_closing_tag_and_not_before(self) -> None:
        page = "<script>var s = '<script>';\n  s += 1;</script>\n   <p>\n   x</p>"
        self.assertEqual(trim_pages.compact(page), "<script>var s = '<script>';\n  s += 1;</script>\n<p>\nx</p>")
        # Inside `<!--`, a `<script` makes the next `</script>` part of the text (HTML's double-escaped state).
        page = "<script><!--<script>\n  </script>\n  x--></script>\n   <p>"
        self.assertEqual(trim_pages.compact(page), "<script><!--<script>\n  </script>\n  x--></script>\n<p>")
        # `-->` leaves the double-escaped state too, so the next `</script>` closes the element, as in browsers.
        page = "<script><!--<script>--></script>\n  x</script>"
        self.assertEqual(trim_pages.compact(page), "<script><!--<script>--></script>\nx</script>")
        page = "<style>p::after { content: '</styles>'; }\n  </style>\n   <p>"
        self.assertEqual(trim_pages.compact(page), "<style>p::after { content: '</styles>'; }\n  </style>\n<p>")

    def test_tag_names_match_whole_names(self) -> None:
        self.assertEqual(trim_pages.compact("<preview>\n  a\n</preview>"), "<preview>\na\n</preview>")

    def test_compacting_twice_changes_nothing(self) -> None:
        page = "<div>\n  <pre>x\n  y</pre>\n    <p>\n  z</p>\n</div>\n"
        once = trim_pages.compact(page)
        self.assertEqual(trim_pages.compact(once), once)


class MovedPageNoticeTests(unittest.TestCase):
    NOTICE = (
        '<h1 id="this-page-moved">This page moved</h1>\n'
        '<div class="bp-moved">\n'
        '<div class="bp-dag-viewer" data-page-href="../roadmap/A/index.html" hidden></div>\n'
        '<p><a href="../roadmap/A/index.html">Continue to the mathematical page</a></p>\n'
        '<script>(function(){var to=new URL("../roadmap/A/index.html",location.href);to.hash=location.hash;'
        "location.replace(to.href);})();</script>\n"
        '<noscript><meta http-equiv="refresh" content="0; url=../roadmap/A/index.html"></noscript>\n'
        "</div>\n"
    )
    CONFIG = types.SimpleNamespace(site_name="ATLAS", theme={"language": "en"})

    def post(self, content: str, title: str = "This page moved") -> str:
        page = types.SimpleNamespace(content=content, title=title)
        return trim_pages.on_post_page("<html>\n  theme\n</html>", page=page, config=self.CONFIG)

    def test_a_moved_page_notice_is_published_without_the_theme(self) -> None:
        document = self.post(self.NOTICE)
        self.assertNotIn("theme", document)
        self.assertTrue(document.startswith('<!doctype html>\n<html lang="en">\n'))
        self.assertIn("<title>This page moved - ATLAS</title>", document)
        self.assertIn(self.NOTICE.strip(), document)

    def test_a_page_with_other_content_keeps_the_theme(self) -> None:
        for content in (
            self.NOTICE.replace("</h1>\n", "</h1>\n<p>Context.</p>\n"),
            self.NOTICE + "<p>More.</p>\n",
            self.NOTICE + "<div>More.</div>\n",
            self.NOTICE.rsplit("</div>", 1)[0],
            # Div-shaped text in comments and in script text is not markup.
            self.NOTICE.replace("<script>", "<!-- <div> --><script>") + "<div><!-- </div> -->More.</div>",
            self.NOTICE.replace("<script>(function(){", "<script>(function(){var d='</div>';") + "<p>More.</p>",
            self.NOTICE.replace('class="bp-moved"', 'class="bp-moved other"'),
            '<h1>Real page</h1><div title="example class=bp-moved"><p>Real text.</p></div>',
            '<h1 id="a">A <em>B</em></h1>\n<div class="bp-moved"></div>',
            '<h1 id="a">A</h1>\n<p>Text.</p>\n',
            "",
        ):
            with self.subTest(content=content):
                self.assertEqual(self.post(content), "<html>\ntheme\n</html>")

    def test_the_title_is_escaped(self) -> None:
        self.assertIn("<title>A &amp; B - ATLAS</title>", self.post(self.NOTICE, title="A & B"))


class NavigationParser(HTMLParser):
    """Read the left navigation as nested entries: (title, href, state, children), plus the TOC links."""

    def __init__(self) -> None:
        super().__init__()
        self.entries: list[list] = []
        self._stack: list[list] = []
        self._depth = 0  # element depth inside the primary navigation, 0 outside it
        self._toc = 0  # element depth inside the drawer's table of contents
        self._link: list | None = None
        self.toc_links: list[str] = []
        self.toc_toggle = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        classes = (values.get("class") or "").split()
        if not self._depth:
            if tag == "nav" and "md-nav--primary" in classes:
                self._depth = 1
            return
        if tag not in {"input", "img", "br"}:
            self._depth += 1
        if self._toc:
            self._toc += tag not in {"input", "img", "br"}
            if tag == "a":
                self.toc_links.append(values.get("href") or "")
            return
        if tag == "nav" and "md-nav--secondary" in classes:
            self._toc = 1
        elif tag == "input" and values.get("id") == "__toc":
            self.toc_toggle = True
        elif tag == "li":
            entry = ["", None, "open" if "md-nav__item--active" in classes else "", []]
            (self._stack[-1][3] if self._stack else self.entries).append(entry)
            self._stack.append(entry)
        elif tag == "a" and self._stack and self._stack[-1][1] is None:
            entry = self._stack[-1]
            entry[1] = values.get("href")
            if "md-nav__link--active" in classes:
                entry[2] = "current"
            self._link = entry

    def handle_endtag(self, tag: str) -> None:
        if not self._depth:
            return
        self._depth -= 1
        if self._toc:
            self._toc -= 1
            return
        if tag == "a":
            self._link = None
        elif tag == "li" and self._stack:
            self._stack.pop()

    def handle_data(self, data: str) -> None:
        if self._link is not None and not self._toc:
            self._link[0] += data.strip()


class NavigationTests(unittest.TestCase):
    """Build a small site with the repository's configuration and theme, and read each page's navigation."""

    SUMMARY = (
        "- [Home](index.md)\n"
        "- Mathematics\n"
        "    - [ATLAS roadmap](roadmap/README.md)\n"
        "        - [Subject A](roadmap/A/README.md)\n"
        "            - [Field F](roadmap/A/f/README.md)\n"
        "                - [Topic T1](roadmap/A/f/t1/README.md)\n"
        "                - [Topic T2](roadmap/A/f/t2/README.md)\n"
        "                    - [Leaf](roadmap/A/f/t2/leaf.md)\n"
        "            - [Field G](roadmap/A/g/README.md)\n"
        "        - [Subject B](roadmap/B/README.md)\n"
        "        - [ATLAS coverage](coverage/README.md)\n"
    )
    PAGES = {
        "index.md": "# Home\n",
        "roadmap/README.md": "# ATLAS roadmap\n",
        "roadmap/A/README.md": "# Subject A\n",
        "roadmap/A/f/README.md": "# Field F\n\n## Overview\n",
        "roadmap/A/f/t1/README.md": "# Topic T1\n\n## Heading\n",
        "roadmap/A/f/t2/README.md": "# Topic T2\n",
        "roadmap/A/f/t2/leaf.md": "# Leaf\n\n## Part\n",
        "roadmap/A/g/README.md": "# Field G\n",
        "roadmap/B/README.md": "# Subject B\n",
        "coverage/README.md": "# ATLAS coverage\n",
    }

    @classmethod
    def setUpClass(cls) -> None:
        from mkdocs.commands.build import build
        from mkdocs.config import load_config

        temporary = tempfile.TemporaryDirectory(prefix="atlas-site-navigation-")
        cls.addClassCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for path, text in {**cls.PAGES, "SUMMARY.md": cls.SUMMARY}.items():
            (root / "docs" / path).parent.mkdir(parents=True, exist_ok=True)
            (root / "docs" / path).write_text(text, encoding="utf-8")
        cls.site = root / "site"
        logging.getLogger("mkdocs").setLevel(logging.ERROR)
        config = load_config(str(ROOT / "mkdocs.yml"), docs_dir=str(root / "docs"), site_dir=str(cls.site))
        build(config)

    def navigation(self, page: str) -> NavigationParser:
        parser = NavigationParser()
        parser.feed((self.site / page).read_text(encoding="utf-8"))
        return parser

    def outline(self, page: str) -> list:
        """The entries as (title, target page, state, children), targets resolved from the page."""

        def resolve(entries):
            return [
                (title, posixpath.normpath(posixpath.join(posixpath.dirname(page), href)), state, resolve(children))
                for title, href, state, children in entries
            ]

        return resolve(self.navigation(page).entries)

    def test_a_topic_page_lists_its_ancestors_siblings_and_table_of_contents(self) -> None:
        page = "roadmap/A/f/t1/index.html"
        self.assertEqual(self.outline(page), [
            ("Home", "index.html", "", []),
            ("ATLAS roadmap", "roadmap/index.html", "open", [
                ("Subject A", "roadmap/A/index.html", "open", [
                    ("Field F", "roadmap/A/f/index.html", "open", [
                        ("Topic T1", page, "current", []),
                        ("Topic T2", "roadmap/A/f/t2/index.html", "", []),
                    ]),
                ]),
            ]),
        ])
        navigation = self.navigation(page)
        self.assertTrue(navigation.toc_toggle)
        self.assertEqual(navigation.toc_links, ["#heading"])

    def test_a_section_page_lists_its_own_entries_and_has_no_drawer_table_of_contents(self) -> None:
        self.assertEqual(self.outline("roadmap/A/f/index.html"), [
            ("Home", "index.html", "", []),
            ("ATLAS roadmap", "roadmap/index.html", "open", [
                ("Subject A", "roadmap/A/index.html", "open", [
                    ("Field F", "roadmap/A/f/index.html", "current", [
                        ("Topic T1", "roadmap/A/f/t1/index.html", "", []),
                        ("Topic T2", "roadmap/A/f/t2/index.html", "", []),
                    ]),
                    ("Field G", "roadmap/A/g/index.html", "", []),
                ]),
            ]),
        ])
        navigation = self.navigation("roadmap/A/f/index.html")
        self.assertFalse(navigation.toc_toggle)
        self.assertEqual(navigation.toc_links, [])

    def test_a_page_inside_a_section_lists_the_section_chain(self) -> None:
        page = "roadmap/A/f/t2/leaf.html"
        self.assertEqual(self.outline(page), [
            ("Home", "index.html", "", []),
            ("ATLAS roadmap", "roadmap/index.html", "open", [
                ("Subject A", "roadmap/A/index.html", "open", [
                    ("Field F", "roadmap/A/f/index.html", "open", [
                        ("Topic T2", "roadmap/A/f/t2/index.html", "open", [
                            ("Leaf", page, "current", []),
                        ]),
                    ]),
                ]),
            ]),
        ])
        self.assertEqual(self.navigation(page).toc_links, ["#part"])

    def test_the_top_pages_list_the_top_entries(self) -> None:
        self.assertEqual(self.outline("index.html"), [
            ("Home", "index.html", "current", []),
            ("ATLAS roadmap", "roadmap/index.html", "", []),
        ])
        self.assertEqual(self.outline("roadmap/index.html"), [
            ("Home", "index.html", "", []),
            ("ATLAS roadmap", "roadmap/index.html", "current", [
                ("Subject A", "roadmap/A/index.html", "", []),
                ("Subject B", "roadmap/B/index.html", "", []),
                ("ATLAS coverage", "coverage/index.html", "", []),
            ]),
        ])
        self.assertEqual(self.outline("coverage/index.html"), [
            ("Home", "index.html", "", []),
            ("ATLAS roadmap", "roadmap/index.html", "open", [
                ("Subject A", "roadmap/A/index.html", "", []),
                ("Subject B", "roadmap/B/index.html", "", []),
                ("ATLAS coverage", "coverage/index.html", "current", []),
            ]),
        ])


if __name__ == "__main__":
    unittest.main()
