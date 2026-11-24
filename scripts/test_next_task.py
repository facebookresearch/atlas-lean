#!/usr/bin/env python3
"""next_task.py picks ready tasks that no pull request names, offline: GitHub and the site are stubbed."""

from __future__ import annotations

import gzip
import io
import json
import os
import re
import sys
import tempfile
import unittest
import urllib.error
import urllib.request
from contextlib import redirect_stderr, redirect_stdout
from email.message import Message
from html import escape
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import next_task  # noqa: E402

REPO = "facebookresearch/atlas-lean"
# The committed priorities, which only the test of their names reads: the others run with a missing file instead.
COMMITTED = next_task.PRIORITIES


def setUpModule() -> None:
    folder = tempfile.TemporaryDirectory()
    unittest.addModuleCleanup(folder.cleanup)
    patch = mock.patch.object(next_task, "PRIORITIES", Path(folder.name) / "priorities.json")
    patch.start()
    unittest.addModuleCleanup(patch.stop)
OPEN = f"{next_task.API}/repos/{REPO}/pulls?state=open&per_page=100&page="
CLOSED = f"{next_task.API}/repos/{REPO}/pulls?state=closed&sort=updated&direction=desc&per_page=100&page="


def item(number: int, phase: str, declaration: str) -> dict:
    """A task as `autoform work list --json` writes one."""
    return {
        "article_id": f"af_{number:024x}", "article_path": f"blueprint/roadmap/Algebra/t{number}.md",
        "article_revision": "0" * 64, "assumes": [], "blockers": [], "claim_target": f"af_{number:024x}",
        "dependencies": [], "lean_targets": [{"declaration": declaration, "source_file": None}],
        "node_id": f"Algebra/t{number}", "open_statements": False, "phase": phase, "ready": True,
        "revision": False, "source_targets": [], "state": "can_prove" if phase == "proof" else "can_state",
        "title": f"Task {number}",
    }


ITEMS = [
    item(1, "proof", "Ext.p1"),
    item(2, "statement", "Ext.s1"),
    item(3, "proof", "Ext.p2"),        # its article id is in an open pull request's body
    item(4, "proof", "Ext.p3.sub"),    # a longer name than the one a pull request gives
    item(5, "statement", "Ext.s2"),    # an open pull request's branch names it
    item(6, "proof", "Ext.p4"),        # a pull request merged after the list's commit names it
    item(7, "proof", "Ext.p5"),        # only a pull request merged before that commit, and one closed unmerged, do
    item(8, "proof", "Ext.p3"),        # an open pull request's title names it, with a stop after it
]
TASKS = {"schema": "autoform-work/v2", "open_statements": False, "source_revision": "f" * 64, "items": ITEMS,
         "commit": "c" * 40, "commit_date": "2026-11-20T12:00:00+00:00", "autoform_ref": "a" * 40}


def pull(number: int, title: str = "", body: str | None = "", branch: str = "topic", merged_at: str | None = None,
         updated_at: str = "2026-11-21T00:00:00Z", base: str = "main", html: str | None = None) -> dict:
    """A pull request as the API lists it with next_task.RENDERED: *html* is its body as GitHub renders it, by default
    a paragraph of text, which holds no code."""
    if html is None and body:
        html = f"<p>{escape(body)}</p>"
    return {"number": number, "title": title, "body": body, "body_html": html, "head": {"ref": branch},
            "base": {"ref": base}, "merged_at": merged_at, "updated_at": updated_at}


def inline(body: str) -> str:
    """A paragraph with code spans in single backticks, as GitHub renders it."""
    return "<p>" + re.sub(r"`([^`]+)`", r"<code>\1</code>", escape(body)) + "</p>"


OPEN_PULLS = [
    pull(1, body=f"Proves it.\n\nTask: {ITEMS[2]['article_id']}"),
    pull(2, branch="someone/Ext.s2"),
    pull(3, title="Prove Ext.p3.", body=None),
    # An id with one more digit is another id.
    pull(9, body=f"See {ITEMS[0]['article_id']}0."),
]
CLOSED_PULLS = [
    pull(4, body=f"Done: `{ITEMS[5]['lean_targets'][0]['declaration']}`", merged_at="2026-11-20T18:00:00Z",
         updated_at="2026-11-20T18:00:00Z"),
    pull(5, body="Ext.p5", merged_at="2026-11-20T11:00:00Z", updated_at="2026-11-20T11:30:00Z"),
    pull(6, body="Ext.p5", merged_at=None, updated_at="2026-11-20T11:00:00Z"),
]


class Site:
    """The site and GitHub's API, as next_task.request reads them."""

    def __init__(self, tasks: dict | None = None, open_pages=(OPEN_PULLS,), closed_pages=(CLOSED_PULLS,)) -> None:
        self.pages = {next_task.TASKS: json.dumps(tasks or TASKS).encode()}
        for prefix, pages in ((OPEN, open_pages), (CLOSED, closed_pages)):
            for number, rows in enumerate(pages, 1):
                self.pages[f"{prefix}{number}"] = json.dumps(rows).encode()
        self.read: list[tuple[str, str | None]] = []
        self.media: list[str] = []

    def __call__(self, url: str, token: str | None = None, media: str | None = None) -> bytes:
        self.read.append((url, token))
        if url.startswith(next_task.API):
            self.media.append(media)
        return self.pages.get(url, b"[]")


def run(site: Site, *args: str, env: dict | None = None, priorities: Path | None = None) -> tuple[int, str, str]:
    """next_task.py's exit code, output and errors, with *priorities* as the checkout's priorities file if given, and
    otherwise the missing one setUpModule sets."""
    out, err = io.StringIO(), io.StringIO()
    with mock.patch.object(next_task, "request", site), mock.patch.dict(os.environ, env or {}, clear=True), \
            mock.patch.object(next_task, "PRIORITIES", priorities or next_task.PRIORITIES), \
            redirect_stdout(out), redirect_stderr(err):
        code = next_task.main(list(args))
    return code, out.getvalue(), err.getvalue()


class Picking(unittest.TestCase):
    def test_tasks_a_pull_request_names_are_skipped_and_statements_come_first(self) -> None:
        site = Site()
        code, out, err = run(site, "--json", "-n", "10")
        self.assertEqual((code, err), (0, ""))
        result = json.loads(out)
        self.assertEqual([task["node_id"] for task in result["next"]], ["Algebra/t2", "Algebra/t1", "Algebra/t4",
                                                                        "Algebra/t7"])
        # The tasks come as tasks.json has them, for agents.
        self.assertEqual(result["next"][0], ITEMS[1])
        self.assertEqual(result["taken_by"], [{"node_id": "Algebra/t3", "pull_requests": [1]},
                                              {"node_id": "Algebra/t5", "pull_requests": [2]},
                                              {"node_id": "Algebra/t6", "pull_requests": [4]},
                                              {"node_id": "Algebra/t8", "pull_requests": [3]}])
        self.assertEqual((result["ready"], result["taken"], result["free"]), (8, 4, 4))
        self.assertEqual((result["commit"], result["autoform_ref"]), ("c" * 40, "a" * 40))
        # One page of each kind, as each holds fewer than a full page; no token was set. They come with their bodies as
        # GitHub renders them.
        self.assertEqual(site.read, [(next_task.TASKS, None), (OPEN + "1", None), (CLOSED + "1", None)])
        self.assertEqual(site.media, [next_task.RENDERED] * 2)

    def test_the_text_lists_the_next_n_with_what_takes_them(self) -> None:
        code, out, _ = run(Site(), "-n", "2")
        self.assertEqual(code, 0)
        self.assertIn(f"8 ready tasks at {'c' * 12}; pull requests take 4 of them, so 4 are free.", out)
        self.assertIn("statement: Task 2\n  article id   af_000000000000000000000002\n  node         Algebra/t2\n"
                      "  Lean         Ext.s1\n  article      blueprint/roadmap/Algebra/t2.md", out)
        self.assertIn("proof: Task 1", out)
        self.assertNotIn("Task 4", out)
        self.assertIn("open a draft pull request that names its article id", out)

    def test_no_field_of_the_list_reaches_the_terminal_unescaped(self) -> None:
        # A list is a download or a file: control characters in it must not steer the terminal or forge lines.
        evil = "\x1b]0;owned\x07\nforged: line\x9b2J"
        task = {**item(1, "statement", "Ext.e" + evil), "title": "T" + evil, "node_id": "Algebra/n" + evil,
                "article_path": "blueprint/roadmap/a" + evil + ".md"}
        tasks = {**TASKS, "items": [task], "commit": "c" + evil}
        code, out, _ = run(Site(tasks=tasks, open_pages=([],), closed_pages=([],)), "-n", "1")
        self.assertEqual(code, 0)
        for character in ("\x1b", "\x07", "\x9b", "\nforged"):
            self.assertNotIn(character, out)
        self.assertIn("T\\x1b]0;owned\\x07\\nforged: line\\x9b2J", out)
        code, out, _ = run(Site(tasks=tasks, open_pages=([],), closed_pages=([],)), "--json")
        self.assertTrue(out.isascii())
        self.assertEqual(json.loads(out)["next"], [task])

    def test_every_page_of_open_pull_requests_is_read(self) -> None:
        filler = [pull(100 + number) for number in range(100)]
        site = Site(open_pages=(filler, [pull(7, body=ITEMS[0]["article_id"].upper())]))
        _, out, _ = run(site, "--json")
        self.assertIn({"node_id": "Algebra/t1", "pull_requests": [7]}, json.loads(out)["taken_by"])
        self.assertEqual([url for url, _ in site.read if url.startswith(OPEN)], [OPEN + "1", OPEN + "2"])

    def test_closed_pull_requests_are_read_until_they_predate_the_commit(self) -> None:
        recent = [pull(200 + number, updated_at="2026-11-21T09:00:00Z") for number in range(99)]
        recent.append(pull(10, body="Ext.p1", merged_at="2026-11-20T13:00:00Z", updated_at="2026-11-20T13:00:00Z"))
        older = [pull(11, body="Ext.s1", merged_at="2026-11-20T12:30:00Z", updated_at="2026-11-20T12:30:00Z"),
                 *(pull(300 + number, updated_at="2026-11-19T00:00:00Z") for number in range(99))]
        late = [pull(12, body="Ext.p5", merged_at="2026-11-20T15:00:00Z")]
        site = Site(open_pages=([],), closed_pages=(recent, older, late))
        _, out, _ = run(site, "--json")
        taken = {row["node_id"]: row["pull_requests"] for row in json.loads(out)["taken_by"]}
        self.assertEqual(taken, {"Algebra/t1": [10], "Algebra/t2": [11]})
        # The second page ends before the commit, so the third is never read.
        self.assertEqual([url for url, _ in site.read if url.startswith(CLOSED)], [CLOSED + "1", CLOSED + "2"])

    def test_a_pull_request_merged_in_the_commits_second_counts(self) -> None:
        # GitHub's times are to the second, as the commit's: one merged in its second may be missing from the list.
        same = [pull(13, body="Ext.p1", merged_at="2026-11-20T12:00:00Z", updated_at="2026-11-20T12:00:00Z"),
                *(pull(400 + number, updated_at="2026-11-20T12:00:00Z") for number in range(99))]
        before = [pull(14, body="Ext.s1", merged_at="2026-11-20T11:59:59Z", updated_at="2026-11-20T11:59:59Z")]
        site = Site(open_pages=([],), closed_pages=(same, before))
        _, out, _ = run(site, "--json")
        taken = {row["node_id"]: row["pull_requests"] for row in json.loads(out)["taken_by"]}
        self.assertEqual(taken, {"Algebra/t1": [13]})
        # A full page that ends in the commit's second may go on in the next one, so that one is read too.
        self.assertEqual([url for url, _ in site.read if url.startswith(CLOSED)], [CLOSED + "1", CLOSED + "2"])

    def test_a_list_without_a_commit_date_is_checked_against_open_pull_requests_only(self) -> None:
        plain = {key: value for key, value in TASKS.items() if key not in ("commit", "commit_date", "autoform_ref")}
        site = Site(tasks=plain)
        code, out, _ = run(site)
        self.assertEqual(code, 0)
        self.assertFalse([url for url, _ in site.read if url.startswith(CLOSED)])
        self.assertIn("records no commit date, so pull requests merged since it was computed are not read", out)

    def test_a_local_file_is_read(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "tasks.json"
            path.write_text(json.dumps(TASKS))
            site = Site()
            code, out, _ = run(site, "--tasks", str(path), "--json", "-n", "1")
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out)["next"], [ITEMS[1]])
        self.assertNotIn(next_task.TASKS, [url for url, _ in site.read])

    def test_a_list_it_cannot_read_stops_it(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            other = Path(folder) / "other.json"
            other.write_text(json.dumps({**TASKS, "schema": "autoform-work/v3"}))
            broken = Path(folder) / "broken.json"
            broken.write_text("{")
            cases = [(other, "is not a task list as `autoform work list --json` writes it"), (broken, "is not JSON"),
                     (Path(folder) / "missing.json", "missing.json:")]
            # Tasks Autoform does not write, and dates GitHub's cannot be compared with.
            # ITEMS[0] is a proof, which needs a Lean declaration.
            unusable = [{"article_id": None}, {"article_id": ITEMS[0]["article_id"] + "\n"}, {"node_id": " "},
                        {"ready": False, "state": "proved"}, {"phase": "statement"},
                        {"lean_targets": [{"declaration": ""}]}, {"lean_targets": None}, {"lean_targets": []}]
            for number, change in enumerate(unusable):
                path = Path(folder) / f"unusable{number}.json"
                path.write_text(json.dumps({**TASKS, "items": [*ITEMS[1:], {**ITEMS[0], **change}]}))
                cases.append((path, "holds a task without its node, article id, ready phase or Lean declarations"))
            for number, (change, key) in enumerate((({"node_id": ITEMS[1]["node_id"]}, "node_id"),
                                                    ({"article_id": ITEMS[1]["article_id"]}, "article_id"))):
                path = Path(folder) / f"twice{number}.json"
                path.write_text(json.dumps({**TASKS, "items": [*ITEMS[1:], {**ITEMS[0], **change}]}))
                cases.append((path, f"gives two tasks one {key}"))
            empty = Path(folder) / "empty.json"
            empty.write_text(json.dumps({**TASKS, "items": []}))
            cases.append((empty, "lists no task"))
            for number, commit in enumerate((1, ["c" * 40])):
                path = Path(folder) / f"commit{number}.json"
                path.write_text(json.dumps({**TASKS, "commit": commit}))
                cases.append((path, "is not a commit name"))
            for number, date in enumerate(("bad date", "2026-11-21", 5)):
                path = Path(folder) / f"date{number}.json"
                path.write_text(json.dumps({**TASKS, "commit_date": date}))
                cases.append((path, "is not a time with its offset"))
            for source, message in cases:
                code, out, err = run(Site(), "--tasks", str(source))
                self.assertEqual((code, out), (1, ""), source)
                self.assertIn(message, err)

    def test_a_short_name_takes_a_task_only_when_it_says_which(self) -> None:
        sofa = [item(20 + n, "proof", f"Cslib.SquareBoundsWanted.bound{n}Upper") for n in range(6)]
        items = [
            item(11, "proof", "MathlibExt.Analysis.FourierConvergenceWanted.Analysis.fejer"),
            item(12, "proof", "MetaMathlibExt.breuillard_green_tao_approximate_subgroup"),
            item(13, "statement", "MathlibExt.AlgebraicGeometry.JacobianChallengeWanted.c"),
            item(14, "proof", "MetaMathlibExt.IsLexMinimalExtension.add"),
            item(15, "proof", "Ext.A.succ"),
            item(16, "proof", "Ext.B.succ"),
            item(17, "proof", "Cslib.SquareBoundsWanted.naiveUpperThree"),
            item(18, "proof", "MetaMathlibExt.green_tao_density"),
            *sofa,
        ]
        tasks = {**TASKS, "items": items}
        pulls = [
            # As an older pull request claims a statement: its short name in code, with the module it is in.
            pull(31, title="Prove Fejér's theorem",
                 body=(body := "Proves the `fejer` statement in `WantedExt/Analysis/FourierConvergenceWanted.lean`."),
                 html=inline(body)),
            # A distinctive short name in a title.
            pull(32, title="WantedExt: require a finite set in breuillard_green_tao_approximate_subgroup"),
            # A common word, an ambiguous name, a short name without its module, and one in prose.
            pull(33, body=(body := "A Möbius map `S z = (a z + b) / (c z + d)` with `add` and `succ` from `A`."),
                 html=inline(body)),
            pull(34, body=(body := "The naive bound `naiveUpperThree` of `SquareBoundsWanted`, as green_tao_density "
                                   "says."), html=inline(body)),
            # Another declaration that ends with the same name.
            pull(35, body=(body := "Uses `Other.breuillard_green_tao_approximate_subgroup`."), html=inline(body)),
        ]
        self.assertEqual(next_task.taken(items, pulls), {"Algebra/t11": [31], "Algebra/t12": [32]})
        site = Site(tasks=tasks, open_pages=(pulls,), closed_pages=([],))
        _, out, _ = run(site, "--json", "-n", "1")
        self.assertEqual(json.loads(out)["taken"], 2)

    def test_the_last_components_of_a_declaration_take_it_when_no_other_ends_so(self) -> None:
        items = [item(71, "statement", "MathlibExt.Geometry.JacobianChallengeWanted.JacobianChallenge.genus"),
                 item(72, "statement", "MathlibExt.AlgebraicGeometry.JacobianChallengeWanted.JacobianChallenge.genus"),
                 item(73, "statement", "MathlibExt.AlgebraicGeometry.FaltingsWanted.Faltings.genus")]
        self.assertEqual(next_task.taken(items, [pull(81, title="Define Faltings.genus")]), {"Algebra/t73": [81]})
        body = "`Geometry.JacobianChallengeWanted.JacobianChallenge.genus`"
        longer = pull(85, body=body, html=inline(body))
        self.assertEqual(next_task.taken(items, [longer]), {"Algebra/t71": [85]})
        # Two declarations end with `JacobianChallenge.genus` and three with `genus`, and a name in prose is no code.
        self.assertEqual(next_task.taken(items, [pull(82, title="Define JacobianChallenge.genus"),
                                                 pull(83, body="`genus`", html=inline("`genus`")),
                                                 pull(84, body="As in Faltings.genus.")]), {})

    def test_code_is_what_github_renders_as_code(self) -> None:
        name = "breuillard_green_tao_approximate_subgroup"
        items = [item(91, "proof", f"MetaMathlibExt.{name}"), item(92, "proof", "MetaMathlibExt.green_tao_density")]
        # Bodies with what GitHub renders them as (POST /markdown, gfm, in the repository).
        lean = '<div class="highlight highlight-source-lean" dir="auto"><pre class="notranslate">'
        code = '<code class="notranslate">'
        # A code block, highlighted or not and in a quote in a list too, and a code span are code.
        claims = [(f"```lean\n#check {name}\n```", f'{lean}<span class="pl-k">#check</span> {name}</pre></div>'),
                  (f"~~~\n{name}\n~~~", f'<pre class="notranslate">{code}{name}\n</code></pre>'),
                  (f"Proves ``{name}``.", f'<p dir="auto">Proves {code}{name}</code>.</p>'),
                  (f"- > ~~~lean\n  > #check {name}\n  > ~~~\n  > Unlike other_name.",
                   f'<ul dir="auto">\n<li>\n<blockquote>\n{lean}<span class="pl-k">#check</span> {name}</pre></div>\n'
                   '<p dir="auto">Unlike other_name.</p>\n</blockquote>\n</li>\n</ul>')]
        for body, html in claims:
            self.assertEqual(next_task.taken(items, [pull(101, body=body, html=html)]), {"Algebra/t91": [101]}, body)
        # The rest is prose, where the end of a declaration takes nothing: after a block in a list item, whose lines a
        # tab may indent, after a code span whose backslash escapes nothing, and in a link's title or a block that
        # GitHub renders as text. An HTML comment it does not render at all.
        prose = [(f"-   ```lean\n    #check Nat\n    ```\n\nUnlike {name}, this changes `foo`.",
                  f'<ul dir="auto">\n<li>\n{lean}<span class="pl-k">#check</span> Nat</pre></div>\n</li>\n</ul>\n'
                  f'<p dir="auto">Unlike {name}, this changes {code}foo</code>.</p>'),
                 (f"- ~~~lean\n\t#check Nat\n  ~~~\nUnlike {name}, this checks `foo`.",
                  f'<ul dir="auto">\n<li>\n{lean}  <span class="pl-k">#check</span> Nat</pre></div>\n</li>\n</ul>\n'
                  f'<p dir="auto">Unlike {name}, this checks {code}foo</code>.</p>'),
                 (f"Use `C:\\` then {name}, not `foo`.",
                  f'<p dir="auto">Use {code}C:\\</code> then {name}, not {code}foo</code>.</p>'),
                 (f'[note](guide.md "see `{name}`")',
                  f'<p dir="auto"><a href="guide.md" title="see `{name}`">note</a></p>'),
                 (f"<details>\n```\n{name}\n```\n</details>",
                  f"<details><summary>Details</summary>\n```\n{name}\n```\n</details>"),
                 (f"<!-- Remove this example: `{name}`. -->", "")]
        for body, html in prose:
            self.assertEqual(next_task.taken(items, [pull(102, body=body, html=html)]), {}, body)
        # The copy of a block that GitHub keeps in an attribute is no text either.
        copied = f'<div data-snippet-clipboard-copy-content="{name}"><pre>{code}#check Nat</code></pre></div>'
        self.assertEqual(next_task.taken(items, [pull(103, body="```\n#check Nat\n```", html=copied)]), {})
        # A full declaration takes its task wherever the Markdown holds it, in a comment too; text either side of an
        # element that does not run inline is two words; and entities are the characters they stand for.
        for body, html in ((f"<!-- MetaMathlibExt.{name} -->", ""),
                           ("Proves", f"<p>MetaMathlibExt.{name}</p><p>green_tao_density</p>"),
                           ("Proves", f"<p>{code}MetaMathlibExt.{name.replace('_s', '&#95;s')}</code></p>")):
            self.assertEqual(next_task.taken(items, [pull(104, body=body, html=html)]), {"Algebra/t91": [104]}, html)

    def test_code_or_an_image_in_a_word_does_not_join_its_two_sides(self) -> None:
        items = [item(93, "proof", "Demo.map_id"), item(94, "proof", "Demo.map_left_id")]
        # As GitHub renders them (POST /markdown, gfm, in the repository).
        code = '<p dir="auto">Note the added qualifier in Demo.map<code class="notranslate">_left</code>_id.</p>'
        image = ('<p dir="auto">Demo.map<a target="_blank" rel="noopener noreferrer" href="x.png">'
                 '<img src="x.png" alt="x" style="max-width: 100%;"></a>_id</p>')
        for body, html in (("Note the added qualifier in Demo.map`_left`_id.", code),
                           ("Demo.map![x](x.png)_id", image)):
            self.assertEqual(next_task.taken(items, [pull(105, body=body, html=html)]), {}, body)

    def test_a_titles_code_spans_are_read_as_commonmark_reads_them(self) -> None:
        items = [item(45, "proof", "Ext.sum"), item(46, "proof", "Ext.sum?")]
        # In a code span a backslash escapes nothing, so `C:\` is one; out of one, an escaped backslash leaves the
        # backtick after it to open one, and an escaped backtick opens none.
        for title in ("Use `C:\\` and `Ext.sum?`", "A \\\\`Ext.sum?` here", "``Ext.sum?``"):
            self.assertEqual(next_task.taken(items, [pull(57, title=title)]), {"Algebra/t46": [57]}, title)
        self.assertEqual(next_task.taken(items, [pull(58, title="Is it \\`Ext.sum?\\`")]),
                         {"Algebra/t45": [58], "Algebra/t46": [58]})

    def test_a_prime_is_part_of_the_name(self) -> None:
        items = [item(41, "proof", "Ext.sum"), item(42, "proof", "Ext.sum'"), item(43, "proof", "Ext.prod"),
                 item(44, "proof", "Ext.prod'")]
        self.assertEqual(next_task.taken(items, [pull(51, title="Prove Ext.sum'.")]), {"Algebra/t42": [51]})
        self.assertEqual(next_task.taken(items, [pull(52, body="`Ext.sum`, at last.")]), {"Algebra/t41": [52]})
        self.assertEqual(next_task.taken(items, [pull(53, body="Proves 'Ext.prod' and 'Ext.prod''.")]),
                         {"Algebra/t43": [53], "Algebra/t44": [53]})

    def test_names_keep_their_punctuation_in_code_and_lose_prose_marks(self) -> None:
        fejer = "MathlibExt.Analysis.FourierConvergenceWanted.Analysis.fejer"
        items = [item(45, "proof", "Ext.sum"), item(46, "proof", "Ext.sum?"), item(47, "proof", fejer)]
        # In code, "?" ends the name; in prose, it may end the sentence.
        self.assertEqual(next_task.taken(items, [pull(54, body=(body := "Proves `Ext.sum?`."), html=inline(body))]),
                         {"Algebra/t46": [54]})
        self.assertEqual(next_task.taken(items, [pull(55, body="Is it Ext.sum?")]),
                         {"Algebra/t45": [55], "Algebra/t46": [55]})
        # Emphasis around a name, Lean's `_root_.` prefix, and universes after it.
        for body, html in ((f"Proves _{fejer}_.", f"<p>Proves <em>{fejer}</em>.</p>"),
                           (f"Proves `_root_.{fejer}`.", inline(f"Proves `_root_.{fejer}`.")),
                           (f"Proves `{fejer}.{{u}}`.", inline(f"Proves `{fejer}.{{u}}`."))):
            self.assertEqual(next_task.taken(items, [pull(56, body=body, html=html)]), {"Algebra/t47": [56]}, body)

    def test_a_pull_request_merged_into_another_branch_takes_nothing(self) -> None:
        merged = [pull(61, body="Ext.p1", merged_at="2026-11-20T13:00:00Z", updated_at="2026-11-20T13:00:00Z",
                       base="feature")]
        _, out, _ = run(Site(open_pages=([],), closed_pages=(merged,)), "--json")
        self.assertEqual(json.loads(out)["taken_by"], [])

    def test_the_count_is_positive(self) -> None:
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            next_task.main(["-n", "0"])


PRIORITIES = {"schema": next_task.PRIORITIES_SCHEMA, "about": "Test weights.", "default": 1,
              "weights": {"Algebra/t7": 2, "Algebra/t1": 0.5, "Algebra/t2": 0.5}}


class Priorities(unittest.TestCase):
    def write(self, folder: str, data: object, name: str = "priorities.json") -> Path:
        path = Path(folder) / name
        path.write_text(data if isinstance(data, str) else json.dumps(data))
        return path

    def test_the_longest_name_that_starts_a_node_id_gives_its_weight(self) -> None:
        table = {"default": 1, "weights": {"Algebra": 2, "Algebra/rings": 0.5, "Algebra/rings/p": 3, "Number": 5}}
        cases = {"Algebra/t1": 2, "Algebra/rings/x": 0.5, "Algebra/rings/p": 3, "Algebra/rings/p/q": 3,
                 # A name counts only up to a slash: `Algebra` is not the start of `AlgebraicGeometry`.
                 "AlgebraicGeometry/x": 1, "Algebra/ringsx/y": 2, "Number/x": 5, "NumberTheory/x": 1}
        for node_id, expected in cases.items():
            self.assertEqual(next_task.priority({"node_id": node_id}, table), expected, node_id)
        self.assertEqual(next_task.priority({"node_id": "Algebra/t1"}, None), 1)

    def test_statements_still_come_first_then_higher_priorities(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = self.write(folder, PRIORITIES)
            code, out, err = run(Site(), "--json", "-n", "10", "--priorities", str(path))
            self.assertEqual((code, err), (0, ""))
            result = json.loads(out)
            # The free tasks are t2 (a statement), then the proofs t1, t4 and t7 in tasks.json's order.
            self.assertEqual([task["node_id"] for task in result["next"]], ["Algebra/t2", "Algebra/t7", "Algebra/t4",
                                                                            "Algebra/t1"])
            self.assertEqual(result["next"][1], ITEMS[6])
            self.assertEqual(result["priority"], {"Algebra/t2": 0.5, "Algebra/t7": 2, "Algebra/t4": 1,
                                                  "Algebra/t1": 0.5})
            self.assertEqual(result["priorities"], str(path))
            code, out, _ = run(Site(), "-n", "2", "--priorities", str(path))
        self.assertEqual(code, 0)
        self.assertIn(f"Priorities from {path}.", out)
        self.assertIn("proof: Task 7\n  article id   af_000000000000000000000007\n  node         Algebra/t7\n"
                      "  Lean         Ext.p5\n  article      blueprint/roadmap/Algebra/t7.md\n  priority     2", out)
        self.assertNotIn("Task 4", out)

    def test_the_checkouts_file_is_the_default_and_without_it_all_weigh_the_same(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = self.write(folder, PRIORITIES)
            _, out, _ = run(Site(), "--json", "-n", "10", priorities=path)
            self.assertEqual([task["node_id"] for task in json.loads(out)["next"]][:2], ["Algebra/t2", "Algebra/t7"])
            self.assertEqual(json.loads(out)["priorities"], str(path))
            missing = Path(folder) / "missing.json"
            _, out, _ = run(Site(), "--json", "-n", "10", priorities=missing)
            result = json.loads(out)
            self.assertEqual([task["node_id"] for task in result["next"]], ["Algebra/t2", "Algebra/t1", "Algebra/t4",
                                                                            "Algebra/t7"])
            self.assertEqual((result["priorities"], set(result["priority"].values())), (None, {1}))
            _, out, _ = run(Site(), "-n", "1", priorities=missing)
        self.assertIn("No priorities, so all tasks have the same priority.", out)
        self.assertIn("  priority     1", out)

    def test_priorities_are_read_from_a_url_without_the_token(self) -> None:
        url = "https://example.org/priorities.json"
        site = Site()
        site.pages[url] = json.dumps(PRIORITIES).encode()
        code, out, _ = run(site, "--json", "-n", "2", "--priorities", url, env={"GH_TOKEN": "secret"})
        self.assertEqual(code, 0)
        self.assertEqual([task["node_id"] for task in json.loads(out)["next"]], ["Algebra/t2", "Algebra/t7"])
        self.assertIn((url, None), site.read)

    def test_load_priorities_takes_a_path(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = self.write(folder, PRIORITIES)
            self.assertEqual(next_task.load_priorities(path), PRIORITIES)
            self.assertEqual(next_task.load_priorities(str(path)), PRIORITIES)

    def test_priorities_it_cannot_read_stop_it(self) -> None:
        base = {key: value for key, value in PRIORITIES.items() if key != "about"}
        cases = [({**base, "schema": "atlas-task-priorities/v2"}, "is not a list of priorities"),
                 ([base], "is not a list of priorities"),
                 ({**base, "weight": {}}, "has a key it should not: 'weight'"),
                 ({**base, "about": ["text"]}, "its about is not a text"),
                 ({**base, "weights": [["Algebra", 2]]}, "its weights are not an object")]
        for value in (0, -1, "1", True, None):
            cases.append(({**base, "default": value}, "is not a positive number"))
            cases.append(({**base, "weights": {"Algebra": value}}, "is not a positive number"))
        for key in ("", "/Algebra", "Algebra/", "Algebra//rings", " Algebra", "Algebra/rings "):
            cases.append(({**base, "weights": {key: 2}}, "is not a node id or the start of one"))
        texts = [("{", "is not JSON"), ('{"default": NaN}', "is not JSON"),
                 (json.dumps(base).replace('"default": 1', '"default": Infinity'), "is not JSON"),
                 (json.dumps(base)[:-1] + ', "default": 2}', "gives 'default' twice"),
                 (json.dumps(base).replace('"Algebra/t7": 2', '"Algebra/t7": 2, "Algebra/t7": 0.5'),
                  "gives 'Algebra/t7' twice")]
        with tempfile.TemporaryDirectory() as folder:
            sources = [(self.write(folder, data, f"case{number}.json"), message)
                       for number, (data, message) in enumerate(cases + texts)]
            sources.append((Path(folder) / "missing.json", "missing.json:"))
            for source, message in sources:
                code, out, err = run(Site(), "--priorities", str(source))
                self.assertEqual((code, out), (1, ""), source)
                self.assertIn(message, err, source)
                if source.exists():
                    # The checkout's own file is read the same way.
                    code, out, err = run(Site(), priorities=source)
                    self.assertEqual((code, out), (1, ""), source)
                    self.assertIn(message, err, source)

    def test_the_committed_weights_name_subjects_and_fields_of_the_taxonomy(self) -> None:
        # A name the taxonomy does not have, such as one a rename left behind, would weigh nothing.
        taxonomy = json.loads((COMMITTED.parent.parent / "scripts" / "taxonomy.json").read_text())
        places = set(taxonomy["subjects"]) | {f"{subject}/{field['slug']}"
                                              for subject, entry in taxonomy["subjects"].items()
                                              for field in entry.get("fields", [])}
        self.assertEqual(sorted(set(next_task.load_priorities(COMMITTED)["weights"]) - places), [])


class Requests(unittest.TestCase):
    def requests(self, env: dict) -> list:
        sent = []

        def urlopen(request, timeout):
            sent.append(request)
            body = json.dumps(TASKS if request.full_url == next_task.TASKS else []).encode()
            return mock.MagicMock(**{"__enter__.return_value.read.return_value": body})

        with mock.patch.object(next_task.OPENER, "open", urlopen), \
                mock.patch.dict(os.environ, env, clear=True), redirect_stdout(io.StringIO()):
            self.assertEqual(next_task.main([]), 0)
        return sent

    def test_the_token_goes_to_the_github_api_only(self) -> None:
        sent = self.requests({"GH_TOKEN": "secret"})
        self.assertEqual([request.full_url for request in sent], [next_task.TASKS, OPEN + "1", CLOSED + "1"])
        self.assertIsNone(sent[0].get_header("Authorization"))
        for request in sent[1:]:
            self.assertEqual(request.get_header("Authorization"), "Bearer secret")
            self.assertEqual(request.get_header("Accept"), next_task.RENDERED)
        self.assertEqual(self.requests({"GITHUB_TOKEN": "other"})[1].get_header("Authorization"), "Bearer other")

    def test_without_a_token_nothing_is_sent(self) -> None:
        self.assertTrue(all(request.get_header("Authorization") is None for request in self.requests({})))

    def test_a_used_up_limit_says_how_to_go_on(self) -> None:
        headers = Message()
        headers["X-RateLimit-Remaining"] = "0"
        headers["X-RateLimit-Reset"] = "1795300000"

        def urlopen(request, timeout):
            if request.full_url == next_task.TASKS:
                return mock.MagicMock(**{"__enter__.return_value.read.return_value": json.dumps(TASKS).encode()})
            raise urllib.error.HTTPError(request.full_url, 403, "rate limit exceeded", headers, None)

        err = io.StringIO()
        with mock.patch.object(next_task.OPENER, "open", urlopen), \
                mock.patch.dict(os.environ, {}, clear=True), redirect_stdout(io.StringIO()), redirect_stderr(err):
            self.assertEqual(next_task.main([]), 1)
        self.assertIn("GitHub's API limit is used up until 22:26 UTC; set GH_TOKEN", err.getvalue())

    def test_a_redirect_away_from_the_api_drops_the_token(self) -> None:
        handler = next_task.SameOriginRedirects()
        sent = urllib.request.Request(OPEN + "1", headers={"Authorization": "Bearer secret"})
        away = handler.redirect_request(sent, None, 302, "Found", Message(), "https://elsewhere.example/pulls")
        self.assertIsNone(away.get_header("Authorization"))
        same = handler.redirect_request(sent, None, 301, "Moved", Message(), f"{next_task.API}/repositories/1/pulls")
        self.assertEqual(same.get_header("Authorization"), "Bearer secret")

    def test_a_compressed_answer_is_read(self) -> None:
        headers = Message()
        headers["Content-Encoding"] = "gzip"
        sent = []

        def urlopen(request, timeout):
            sent.append(request)
            response = mock.MagicMock()
            response.__enter__.return_value.read.return_value = gzip.compress(json.dumps(TASKS).encode())
            response.__enter__.return_value.headers = headers
            return response

        with mock.patch.object(next_task.OPENER, "open", urlopen):
            self.assertEqual(json.loads(next_task.request(next_task.TASKS)), TASKS)
        self.assertEqual(sent[0].get_header("Accept-encoding"), "gzip")

    def test_an_unreachable_site_says_so(self) -> None:
        def urlopen(request, timeout):
            raise urllib.error.URLError("no route to host")

        err = io.StringIO()
        with mock.patch.object(next_task.OPENER, "open", urlopen), redirect_stdout(io.StringIO()), \
                redirect_stderr(err):
            self.assertEqual(next_task.main([]), 1)
        self.assertEqual(err.getvalue(), f"error: {next_task.TASKS}: no route to host\n")


if __name__ == "__main__":
    unittest.main()
