"""Small navigation-payload regressions for the published-site checker."""

from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

if __package__:
    from . import check_blueprint_site as checker
else:
    import check_blueprint_site as checker


class NavigationPayloadTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="atlas-site-navigation-test-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.docs = root / "docs"
        self.site = root / "site"
        self.docs.mkdir()
        (self.site / "dependencies").mkdir(parents=True)

    def write(self, path: Path, content: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def write_json(self, path: Path, payload: object) -> None:
        self.write(path, json.dumps(payload))

    def check(self) -> tuple[int, str, str]:
        stdout, stderr = io.StringIO(), io.StringIO()
        argv = ["check_blueprint_site.py", str(self.docs), str(self.site)]
        with patch.object(sys, "argv", argv), redirect_stdout(stdout), redirect_stderr(stderr):
            result = checker.main()
        return result, stdout.getvalue(), stderr.getvalue()

    def test_json_urls_finds_navigation_and_book_fields(self) -> None:
        payload = {
            "nodes": [{
                "url": "topic.html#node=lemma",
                "data_url": "topic.json",
                "article_url": "../book.html#lemma",
                "scope": "not-a-url",
                "title": "Not a URL either",
            }],
            "view": {"book": "../book.html"},
            "optional": {"url": None, "data_url": 3},
        }

        self.assertEqual(
            list(checker.json_urls(payload)),
            ["topic.html#node=lemma", "topic.json", "../book.html#lemma", "../book.html"],
        )

    def test_missing_navigation_data_and_book_fragments_fail(self) -> None:
        self.write(self.site / "book.html", '<h1 id="present">Book</h1>')
        cases = (
            ("data_url", "missing.json", "targets missing"),
            ("article_url", "../book.html#absent", "missing fragment"),
            ("book", "../book.html#absent", "missing fragment"),
        )
        for key, href, expected in cases:
            with self.subTest(key=key):
                self.write_json(self.site / "dependencies/index.json", {"nodes": [{key: href}]})
                result, _stdout, stderr = self.check()
                self.assertEqual(result, 1)
                self.assertIn(expected, stderr)
                self.assertIn(href, stderr)

    def test_empty_site_fails(self) -> None:
        result, _stdout, stderr = self.check()
        self.assertEqual(result, 1)
        self.assertIn("0 HTML pages", stderr)

    def test_broken_root_dependency_target_is_checked(self) -> None:
        self.write_json(self.docs / "dependencies.json", {"nodes": []})
        self.write_json(self.site / "dependencies.json", {"nodes": [{"data_url": "missing-root.json"}]})

        result, _stdout, stderr = self.check()

        self.assertEqual(result, 1)
        self.assertIn("dependencies.json", stderr)
        self.assertIn("missing-root.json", stderr)
        self.assertIn("targets missing", stderr)

    def test_valid_navigation_targets_and_book_fragments_succeed(self) -> None:
        card = '<div class="bp-thmwrapper" data-autoform-node-id="lemma"></div>'
        self.write(self.docs / "roadmap/topic/README.md", card)
        self.write(self.site / "roadmap/topic/index.html", '<h1 id="lemma">Lemma</h1>' + card)
        self.write(self.site / "dependencies/topic.html", "<h1>Topic</h1>")
        self.write_json(self.site / "dependencies/topic.json", {"nodes": []})
        self.write_json(self.site / "dependencies/index.json", {
            "nodes": [{
                "url": "topic.html#node=lemma",
                "data_url": "topic.json",
                "article_url": "../roadmap/topic/index.html#lemma",
            }],
            "view": {"book": "../roadmap/topic/index.html"},
        })
        root_payload = {
            "nodes": [{
                "url": "dependencies/topic.html",
                "data_url": "dependencies/topic.json",
                "article_url": "roadmap/topic/index.html#lemma",
            }],
            "view": {"book": "roadmap/topic/index.html#lemma"},
        }
        self.write_json(self.docs / "dependencies.json", root_payload)
        self.write_json(self.site / "dependencies.json", root_payload)

        result, stdout, stderr = self.check()

        self.assertEqual(result, 0, stderr)
        self.assertEqual(stderr, "")
        self.assertTrue(stdout.startswith("OK:"), stdout)


    def site_with_page(self, body: str) -> None:
        card = '<div class="bp-thmwrapper" data-autoform-node-id="lemma"></div>'
        self.write(self.docs / "roadmap/topic/README.md", card)
        self.write(self.site / "roadmap/topic/index.html", f"<h1>Topic</h1>{card}{body}")

    def test_an_unpaired_math_delimiter_fails(self) -> None:
        # A `$$` display that touches its paragraph renders as `$`, inline math, `$`.
        cases = ('<p>So $<span class="arithmatex">\\(x^2\\)</span>$ follows.</p>',
                 "<ul><li>An unclosed $\\mathbb{R} span.</li></ul>", "<p>An unmatched $$ display.</p>",
                 "<p>A closing x^{2}$ without its opening.</p>", "<p>If $2^{\\kappa}\\lt \\lambda, then.</p>",
                 # Inline markup or a comment between the `$` and the TeX does not hide it.
                 "<p>Let $<em>x_i</em> be a number.</p>", "<p>Then <em>x_i</em>$ follows.</p>",
                 '<p>See $<a href="#">x^2</a> here.</p>', "<p>Odd $<!-- note -->x_i here.</p>",
                 # Code between a backslash and a dollar does not escape it.
                 "<p>\\<code> </code>$x_i here.</p>")
        for body in cases:
            with self.subTest(body=body):
                self.site_with_page(body)
                result, _stdout, stderr = self.check()
                self.assertEqual(result, 1)
                self.assertIn("a math delimiter did not pair", stderr)
                self.assertIn("roadmap/topic/index.html", stderr)

    def test_dollars_in_math_code_scripts_and_prose_pass(self) -> None:
        # Math, code and scripts keep their `$`; so does prose that uses it as a currency sign. A literal dollar of
        # delimiter shape is written `&#36;`, and a backslash left in the HTML escapes its dollar.
        self.site_with_page('<p>Math <span class="arithmatex">\\($x$\\)</span>, code <code>a $$ b</code>.</p>'
                            "<pre><span>echo $HOME</pre><p>After the block.</p>"
                            '<script>var s = "$$";</script><div class="arithmatex">\\[ $ \\]</div><br><img alt="x">'
                            '<p>It costs $5, or <a href="#">$3 a month</a>; <span class="arithmatex">\\(x\\)</span> is $2.</p>'
                            "<p>Write &#36;&#36; literally, and &#36;x_i too; &amp; is just an ampersand.</p>"
                            "<p>It costs \\$5, and \\$x_i is escaped.</p><p>A <em>price</em> of $5 and <strong>$6</strong>.</p>"
                            "<p>Total $</p><p>x_i starts the next paragraph.</p><p>A $<code> </code>x_i apart.</p>")
        result, _stdout, stderr = self.check()
        self.assertEqual(result, 0, stderr)


if __name__ == "__main__":
    unittest.main()
