#!/usr/bin/env python3
"""Tests for scripts/graph_batch.py: the parts on their own, then make, verify and base on a repository of a few files
whose main merges pull requests, with copies of the real scripts. Run with a Python that has Autoform installed."""

from __future__ import annotations

import html
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

if __package__:
    from . import graph_batch as batch
    from . import sync_wiki as sync
else:
    import graph_batch as batch
    import sync_wiki as sync

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent


def rendered(text: str) -> str:
    """A description of plain lines as GitHub renders it: paragraphs at blank lines, their lines joined by <br>."""
    paragraphs = [part for part in text.replace("\r\n", "\n").split("\n\n") if part.strip()]
    return "\n".join('<p dir="auto">' + "<br>\n".join(html.escape(line.strip(), quote=False)
                                                       for line in part.strip("\n").split("\n")) + "</p>"
                     for part in paragraphs)


class Trailers(unittest.TestCase):
    def test_both_trailers_once_each(self) -> None:
        base, through = "a" * 40, "b" * 40
        message = f"Sync the graph\n\nText.\n\nGraph-sync-base: {base}\nGraph-sync-through: {through}\n"
        self.assertEqual(batch.trailers(message), {"Graph-sync-base": base, "Graph-sync-through": through})
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base}\n"), {})
        self.assertEqual(batch.trailers(message + f"Graph-sync-through: {'c' * 40}\n"), {})
        # A short or upper-case commit name is no trailer.
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base[:12]}\nGraph-sync-through: {through}\n"), {})
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base.upper()}\nGraph-sync-through: {through}\n"), {})


class PlaceLines(unittest.TestCase):
    def test_lines_of_a_description(self) -> None:
        body = ("Graph: new\r\nPlace: MathlibExt/A/B -> Algebra/groups\r\n"
                "Not a Place: line\n  Place:   MathlibExt/A/C   ->   Algebra/groups | Group basics  \n")
        self.assertEqual(batch.place_lines(body), ["MathlibExt/A/B -> Algebra/groups",
                                                   "MathlibExt/A/C   ->   Algebra/groups | Group basics"])

    def test_lines_the_description_does_not_show_are_left_out(self) -> None:
        body = ("Place: MathlibExt/A/B -> Algebra/groups\n```\nPlace: MathlibExt/A/C -> Algebra/groups\n```\n"
                "~~~text\nPlace: MathlibExt/A/D -> Algebra/groups\n~~~\n<!-- one line: Place: MathlibExt/A/E -> "
                "Algebra/groups -->\n<!--\nPlace: MathlibExt/A/F -> Algebra/groups\n-->\nPlace: MathlibExt/A/G -> "
                "Algebra/rings\n")
        self.assertEqual(batch.place_lines(body), ["MathlibExt/A/B -> Algebra/groups",
                                                   "MathlibExt/A/G -> Algebra/rings"])
        # A longer fence holds a shorter run; an indented code block; a comment opened in the middle of a line.
        for hidden in ("````md\n```\nPlace: MathlibExt/A/B -> Algebra/groups\n```\n````\n",
                       "Example:\n\n    Place: MathlibExt/A/C -> Algebra/groups\n",
                       "Example:\n\n\tPlace: MathlibExt/A/C -> Algebra/groups\n",
                       "text <!--\nPlace: MathlibExt/A/D -> Algebra/groups\n-->\n",
                       "~~~~\n~~~ not a close\nPlace: MathlibExt/A/E -> Algebra/groups\n~~~~\n",
                       # A tab is four columns, a no-break space is no indentation and may not follow a closing fence,
                       # and Markdown ends a line only at a line feed or a carriage return.
                       "```\n\t```\nPlace: MathlibExt/A/B -> Algebra/groups\n```\n",
                       "```\n\u00a0```\nPlace: MathlibExt/A/B -> Algebra/groups\n```\n",
                       "```\n```\u00a0\nPlace: MathlibExt/A/B -> Algebra/groups\n```\n",
                       "Text\u2028Place: MathlibExt/A/B -> Algebra/groups\n",
                       "Text\x0cPlace: MathlibExt/A/B -> Algebra/groups\n"):
            with self.subTest(hidden=hidden):
                self.assertEqual(batch.place_lines(hidden + "Place: MathlibExt/A/G -> Algebra/rings\n"),
                                 ["MathlibExt/A/G -> Algebra/rings"])

    def test_lines_in_lists_quotations_headings_and_tables_are_read_for_the_notes(self) -> None:
        # GitHub shows none of them as a line of plain text, so visible_lines leaves them out: they get a note.
        for line in ("- Place: MathlibExt/A/B -> Algebra/groups", "* Place: MathlibExt/A/B -> Algebra/groups",
                     "1. Place: MathlibExt/A/B -> Algebra/groups", "> Place: MathlibExt/A/B -> Algebra/groups",
                     "> - Place: MathlibExt/A/B -> Algebra/groups", "## Place: MathlibExt/A/B -> Algebra/groups",
                     "| Place: MathlibExt/A/B -> Algebra/groups |"):
            with self.subTest(line=line):
                self.assertEqual(batch.place_lines(line + "\n"), ["MathlibExt/A/B -> Algebra/groups"])
        self.assertEqual(batch.place_lines("- Graph: af_x new\n", batch.GRAPH), ["af_x new"])
        # Emphasis or code around the label.
        for line in ("**Place:** MathlibExt/A/B -> Algebra/groups", "*Place:* MathlibExt/A/B -> Algebra/groups",
                     "`Place: MathlibExt/A/B -> Algebra/groups`", "- **Place:** MathlibExt/A/B -> Algebra/groups"):
            with self.subTest(line=line):
                self.assertEqual(batch.place_lines(line + "\n"), ["MathlibExt/A/B -> Algebra/groups"])

    def test_descriptions_read_with_gh(self) -> None:
        tools = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tools, True)
        answer = {"data": {"repository": {
            "p1": {"number": 1, "body": "Place: A/B -> C/d\n", "bodyHTML": "<p>Place: A/B -&gt; C/d</p>",
                   "mergedAt": "2026-11-26T10:00:00Z", "lastEditedAt": None, "mergeCommit": {"oid": "a" * 40}},
            "p2": {"number": 2, "body": "Edited\n", "bodyHTML": "<p>Edited</p>", "mergedAt": "2026-11-26T10:00:00Z",
                   "lastEditedAt": "2026-11-26T11:00:00Z", "mergeCommit": {"oid": "b" * 40}},
            "p3": {"number": 3, "body": "Elsewhere\n", "bodyHTML": "<p>Elsewhere</p>",
                   "mergedAt": "2026-11-26T10:00:00Z", "lastEditedAt": None, "mergeCommit": {"oid": "f" * 40}}}}}
        (tools / "gh").write_text(f"#!/bin/sh\ncat <<'EOF'\n{json.dumps(answer)}\nEOF\n")
        (tools / "gh").chmod(0o755)
        path = os.environ["PATH"]
        os.environ["PATH"] = f"{tools}:{path}"
        self.addCleanup(os.environ.__setitem__, "PATH", path)
        found = batch.fetch_bodies([(1, "a" * 40), (2, "b" * 40), (3, "c" * 40)])
        # A pull request whose merge commit is not main's is left out; one edited after its merge is marked.
        self.assertEqual(sorted(found), [1, 2])
        self.assertEqual((found[1], found[1].html, found[1].edited), ("Place: A/B -> C/d\n", "<p>Place: A/B -&gt; C/d</p>",
                                                                      False))
        self.assertTrue(found[2].edited)

    def test_the_lines_github_shows_as_plain_text(self) -> None:
        # As GitHub renders descriptions: lines joined into a paragraph with <br>, entities escaped.
        shown = ('<p dir="auto">Graph: new<br>\nPlace: MathlibExt/A/B -&gt; Algebra/groups | Rings &amp; fields</p>\n'
                 '<p dir="auto">Place: MathlibExt/A/C -&gt; Algebra/groups</p>')
        self.assertEqual(batch.visible_lines(shown), ["MathlibExt/A/B -> Algebra/groups | Rings & fields",
                                                      "MathlibExt/A/C -> Algebra/groups"])
        for hidden in ('<div class="highlight"><pre>Place: MathlibExt/A/B -&gt; Algebra/groups</pre></div>',
                       '<pre><code>Place: MathlibExt/A/B -&gt; Algebra/groups\n</code></pre>',
                       '<ul dir="auto">\n<li>Place: MathlibExt/A/B -&gt; Algebra/groups</li>\n</ul>',
                       '<blockquote>\n<p dir="auto">Place: MathlibExt/A/B -&gt; Algebra/groups</p>\n</blockquote>',
                       '<details><summary>More</summary>\n<p dir="auto">Place: MathlibExt/A/B -&gt; Algebra/groups</p>'
                       '\n</details>',
                       '<p dir="auto">Place: <code>MathlibExt/A/B</code> -&gt; Algebra/groups</p>',
                       '<p dir="auto">Place: MathlibExt/A/B -&gt; Algebra/groups <em>now</em></p>',
                       '<p dir="auto"><em>Note<br>\nPlace: MathlibExt/A/B -&gt; Algebra/groups</em></p>',
                       '<p dir="auto">Text Place: MathlibExt/A/B -&gt; Algebra/groups</p>'):
            with self.subTest(hidden=hidden):
                self.assertEqual(batch.visible_lines(hidden + '\n<p dir="auto">Place: MathlibExt/A/G -&gt; '
                                                     'Algebra/rings</p>'), ["MathlibExt/A/G -> Algebra/rings"])

    def test_a_module_a_field_and_maybe_a_topic(self) -> None:
        self.assertEqual(batch.parse_place("MathlibExt/Algebra/Rings -> Algebra/groups"),
                         ("MathlibExt/Algebra/Rings", "Algebra/groups", None))
        self.assertEqual(batch.parse_place("MathlibExt/Algebra/Rings -> Algebra/groups/finite | Rings: a, b (c) – d's"),
                         ("MathlibExt/Algebra/Rings", "Algebra/groups/finite", "Rings: a, b (c) – d's"))

    def test_anything_else_is_refused_without_repeating_it(self) -> None:
        for value in ("MathlibExt/Algebra/Rings Algebra/groups",
                      "MathlibExt/Algebra/Rings ->",
                      "MathlibExt/Algebra/Rings -> Algebra/groups |",
                      "MathlibExt/Algebra/Rings -> Algebra/groups extra words",
                      "Mathlib/Algebra/Group -> Algebra/groups",
                      "MathlibExt/Algebra/Rings.lean -> Algebra/groups",
                      "MathlibExt -> Algebra/groups",
                      "MathlibExt\\Algebra\\Rings -> Algebra/groups",
                      "@octocat -> Algebra/groups",
                      "MathlibExt/Algebra/R@x -> Algebra/groups",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | " + "T" * 161,
                      "MathlibExt/Algebra/Rings -> Algebra/groups | T\x07",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | Fixes #1",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | cc @octocat",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | Units <b>x</b>",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | Rings: a | b",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | [Rings](x)",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | `Rings`",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | Fixes https://example.invalid/issues/1"):
            with self.subTest(value=value), self.assertRaises(ValueError) as caught:
                batch.parse_place(value)
            for part in value.split():
                if len(part) >= 5:
                    self.assertNotIn(part, str(caught.exception))


TAXONOMY_TEXT = ('{\n "schema": "atlas-wiki-taxonomy/v1",\n "subjects": {"Algebra": {"fields": []}},\n'
                 ' "placements": {\n'
                 '  "MathlibExt/B": {"to": "Algebra/groups", "title": "B"},\n'
                 '  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n'
                 '  "MathlibExt/C": {"to": "Algebra/groups", "title": "C"}\n'
                 ' },\n "mathlib_exclusions": {}\n}\n')


class EditPlacements(unittest.TestCase):
    def test_an_entry_goes_after_the_last_one_before_it(self) -> None:
        spot = {"to": "Algebra/groups", "title": "Ç"}
        edited = batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/Ca": spot}, [])
        # After MathlibExt/C, the last entry before it in the file's own order, which is not sorted: one line added,
        # and a comma where a line stopped being the last.
        self.assertEqual(edited, TAXONOMY_TEXT.replace(
            '"title": "C"}\n', '"title": "C"},\n  "MathlibExt/Ca": {"to": "Algebra/groups", "title": "Ç"}\n'))
        # After the greatest module before its own, MathlibExt/D, wherever the file has it, not after the last line
        # whose module sorts before it.
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/E": spot}, []), TAXONOMY_TEXT.replace(
            '"title": "D"},\n', '"title": "D"},\n  "MathlibExt/E": {"to": "Algebra/groups", "title": "Ç"},\n'))
        first = batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/A": spot}, [])
        self.assertEqual(first, TAXONOMY_TEXT.replace(
            ' "placements": {\n', ' "placements": {\n  "MathlibExt/A": {"to": "Algebra/groups", "title": "Ç"},\n'))
        self.assertEqual(json.loads(first)["placements"]["MathlibExt/A"], spot)

    def test_a_dropped_entry_takes_only_its_line(self) -> None:
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/D"]),
                         TAXONOMY_TEXT.replace('  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n', ""))
        # The last entry: the one before it loses its comma.
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/C"]),
                         TAXONOMY_TEXT.replace('"title": "D"},\n  "MathlibExt/C": {"to": "Algebra/groups", "title": "C"}\n',
                                               '"title": "D"}\n'))
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, []), TAXONOMY_TEXT)

    def test_it_refuses_what_it_cannot_do_exactly(self) -> None:
        spot = {"to": "Algebra/groups", "title": "B"}
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/B": spot}, [])
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/Z"])
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT.replace('  "MathlibExt/D"', '  "MathlibExt/D" '), {}, [])

    def test_an_entry_over_several_lines_keeps_them(self) -> None:
        text = TAXONOMY_TEXT.replace('  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n',
                                     '  "MathlibExt/D": {\n    "to": "Algebra/groups",\n    "title": "D"\n  },\n')
        spot = {"to": "Algebra/groups", "title": "E"}
        self.assertEqual(batch.edit_placements(text, {}, []), text)
        # After it, the new line; its own lines, comma included, stay as they are.
        self.assertEqual(batch.edit_placements(text, {"MathlibExt/E": spot}, []), text.replace(
            '"title": "D"\n  },\n', '"title": "D"\n  },\n  "MathlibExt/E": {"to": "Algebra/groups", "title": "E"},\n'))
        # Dropped, it loses all its lines; as the last entry, it gains or loses only its comma.
        self.assertEqual(batch.edit_placements(text, {}, ["MathlibExt/D"]), TAXONOMY_TEXT.replace(
            '  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n', ""))
        last = text.replace('  },\n  "MathlibExt/C": {"to": "Algebra/groups", "title": "C"}\n', '  }\n')
        self.assertEqual(batch.edit_placements(text, {}, ["MathlibExt/C"]), last)
        self.assertEqual(batch.edit_placements(last, {"MathlibExt/Z": spot}, []), last.replace(
            '"title": "D"\n  }\n', '"title": "D"\n  },\n  "MathlibExt/Z": {"to": "Algebra/groups", "title": "E"}\n'))
        with self.assertRaises(ValueError):
            batch.edit_placements(text.replace('    "title": "D"\n  },\n', '    "title": "D"\n'), {}, [])

    def test_the_committed_taxonomy_round_trips(self) -> None:
        text = (ROOT / "scripts" / "taxonomy.json").read_text(encoding="utf-8")
        self.assertEqual(batch.edit_placements(text, {}, []), text)


class ReportSections(unittest.TestCase):
    def test_the_items_of_each_section_the_sync_prints(self) -> None:
        titles = dict(sync.REPORT)
        output = (f"{titles['added']}: 2\n  a.md\n  b.md\n{titles['replaced']}: 1\n  Algebra/x: - [Old](old.md)\n"
                  f"{titles['appended']}: 0\nerror: something\n  not an item\n")
        self.assertEqual(batch.report_sections(output), {"added": ["a.md", "b.md"],
                                                         "replaced": ["Algebra/x: - [Old](old.md)"], "appended": []})


class InTopic(unittest.TestCase):
    def test_a_page_in_the_topic_or_alone_in_the_field(self) -> None:
        for page, expected in (("Algebra/groups/sylow-theorems/sylow.md", True),
                               ("Algebra/groups/part-02/sylow-theorems/part-01/sylow.md", True),
                               ("Algebra/groups/sylow.md", True), ("Algebra/groups/part-03/sylow.md", True),
                               ("Algebra/groups/group-basics/sylow.md", False),
                               ("Algebra/groups-extra/sylow-theorems/sylow.md", False),
                               ("Algebra/not-yet-classified/sylow/sylow.md", False)):
            with self.subTest(page=page):
                self.assertEqual(batch.in_topic(page, "Algebra/groups", "Sylow theorems"), expected)


class Fields(unittest.TestCase):
    def test_fields_and_subfields(self) -> None:
        taxonomy = {"subjects": {"Algebra": {"fields": [{"slug": "groups", "subfields": [{"slug": "finite"}]},
                                                        {"slug": "rings", "subfields": []}]}}}
        self.assertEqual(batch.fields_of(taxonomy), {"Algebra/groups", "Algebra/groups/finite", "Algebra/rings"})


class Describe(unittest.TestCase):
    def describe(self, plan=None, links=None, report=None, full=False) -> str:
        with patch.object(batch, "changed_between", return_value=[]):
            return batch.describe("c" * 40, "b" * 40, "h" * 40, plan or batch.PlacementPlan(), report or {}, {},
                                  links or batch.LinkPlan(), full=full)

    def test_the_pages_linked_already_fit_in_a_description(self) -> None:
        pointer = f"`python3 scripts/graph_batch.py verify {'c' * 40}`, run from a checkout of `main`, prints them all."
        # Their ids, by pull request, while the description stays short enough for GitHub.
        short = self.describe(links=batch.LinkPlan(linked={"af_" + "1" * 24: [7, 9], "af_" + "2" * 24: [7]}))
        self.assertIn(f"Pages linked already, 2, by the pull request that names them:\n\n```text\n#7: af_{'1' * 24} "
                      f"af_{'2' * 24}\n#9: af_{'1' * 24}\n```\n", short)
        self.assertNotIn(pointer, short)
        # Else how many, with what the other ids are, the pull requests aside, and where to read them in full.
        # The reasons say which pages a page's own dependency sections link, and which declaration a page holds back:
        # the short form counts the pages by the kind of reason.
        gaps = [(f"af_{number:024x}", [8 + number % 2], f"its own dependency sections link {1 + number % 3} page(s), "
                 f"such as `../p{number}.md`, and the batch cannot tell whether the declaration's Lean records them: "
                 f"linking it is an editor's call; #{8 + number % 2} adds no candidate the batch would give a page")
                for number in range(3000, 3100)]
        held = [(f"af_{number:024x}", [10], f"it holds `Ext.held_{number}` back: relinking it is an editor's call; #10 "
                 "adds no candidate the batch would give a page") for number in range(3100, 3105)]
        links = batch.LinkPlan(linked={f"af_{number:024x}": [7] for number in range(3000)},
                               unchanged=gaps + held + [("af_" + "f" * 24, [9], "no row has this article id")])
        long = self.describe(links=links)
        self.assertIn("### Pages named on `Graph:` lines, left as they are\n\n3000 ids name pages linked already; 5 ids: "
                      "it holds … back: relinking it is an editor's call; #N adds no candidate the batch would give a "
                      "page; 100 ids: its own dependency sections link other pages, and the batch cannot tell whether "
                      "the declaration's Lean records them: linking it is an editor's call; #N adds no candidate the "
                      f"batch would give a page; 1 ids: no row has this article id, too many to list here: {pointer}\n",
                      long)
        self.assertLess(len(long), batch.BODY_LIMIT)
        whole = self.describe(links=links, full=True)
        self.assertIn(f"af_{'f' * 24} (#9): no row has this article id", whole)
        self.assertIn("such as ../p3000.md, and the batch", whole)
        self.assertGreater(len(whole), batch.BODY_LIMIT)

    def test_the_kind_of_a_reason(self) -> None:
        self.assertEqual(batch.reason_kind("its own dependency sections link 3 page(s), such as `../a b.md`, and the "
                                           "batch cannot tell whether the declaration's Lean records them: linking it is "
                                           "an editor's call; #9102 adds no candidate the batch would give a page"),
                         "its own dependency sections link other pages, and the batch cannot tell whether the "
                         "declaration's Lean records them: linking it is an editor's call; #N adds no candidate the "
                         "batch would give a page")
        # A fixed word in code stays, without its backticks, as in the full form.
        self.assertEqual(batch.reason_kind("#7 adds one documented declaration in its topic that could state it, "
                                           "`Ext.a`, which `main` had before this batch's base"),
                         "#N adds one documented declaration in its topic that could state it, …, which main had before "
                         "this batch's base")
        self.assertEqual(batch.reason_kind("#9937, #10600 name it, and the batch does not choose between them"),
                         "#N name it, and the batch does not choose between them")
        self.assertEqual(batch.reason_kind("no row has this article id"), "no row has this article id")

    def test_the_line_of_a_page_left_for_an_editor(self) -> None:
        # The page, the pull requests that name it, outside code, the short names of its reason, how many it withholds.
        self.assertEqual(batch.left_line("A/b.md", "#9937, #10600 name it, and the batch does not choose between them; "
                                         "it is a node still to expand: expanding or linking it is an editor's call",
                                         ["Ext.a", "Ext.b"]),
                         "- `A/b.md`, #9937, #10600: several pull requests name it; a node still to expand; 2 given no "
                         "page")
        self.assertEqual(batch.left_line("A/b.md", "#10533 names it; its own dependency sections link 3 page(s), such as "
                                         "`#12.md`, and the batch cannot tell whether the declaration's Lean records "
                                         "them: linking it is an editor's call", ["Ext.a"]),
                         "- `A/b.md`, #10533: its own dependency sections link pages; 1 given no page")
        self.assertEqual(batch.left_line("A/b.md", "`Ext.a`, the one declaration in its topic that #26 adds and that could "
                                         "state it, is gone or deprecated on `main` now: compare what replaced it, if "
                                         "anything, with the page", []),
                         "- `A/b.md`, #26: its one candidate is gone or deprecated")
        # A reason none of the phrases names is given by its kind.
        self.assertEqual(batch.left_line("A/b.md", "#7 names it; a reason no phrase names, `A/c.md`", ["Ext.a"]),
                         "- `A/b.md`, #7: a reason no phrase names, …; 1 given no page")

    def test_the_description_keeps_within_any_bound_its_short_forms_keep_within(self) -> None:
        # Lists that give way before the pages left for an editor, which withhold many names each: for every bound that
        # the description keeps within with every list given way (the pages left for an editor a line each), make's
        # description keeps within it too; past the bound, it gives every list that can give way as a count.
        plan = batch.PlacementPlan(added=[batch.Placement(f"MathlibExt/A/M{number}", "Algebra/groups", f"Topic {number}",
                                                          f"#{number}") for number in range(300)],
                                   dropped=[f"MathlibExt/Gone/M{number}" for number in range(300)])
        links = batch.LinkPlan(left=[(f"af_{page:024x}", f"Algebra/groups/topic-{page}/p{page}.md",
                                      f"#{page} adds 40 documented declarations in its topic that could state it",
                                      [f"Ext.topic{page}.name_{name}" for name in range(40)]) for page in range(60)])
        report = {"missing": [f"Ext.n{number}" for number in range(400)],
                  "new": {f"Ext.n{number}": f"MathlibExt/A/M{number}" for number in range(400)}}
        whole = self.describe(plan, links, report, full=True)
        with patch.object(batch, "BODY_LIMIT", 0):
            floor = self.describe(plan, links, report)
        self.assertIn("- `Algebra/groups/topic-0/p0.md`, #0: several candidates in its topic; 40 given no page\n", floor)
        self.assertLess(len(floor), len(whole) // 4)
        for limit in range(len(floor), len(whole) + 2, 97):
            with self.subTest(limit=limit), patch.object(batch, "BODY_LIMIT", limit):
                text = self.describe(plan, links, report)
                self.assertLessEqual(len(text), limit)
                # The pages left for an editor keep their names while any other list can still give way.
                if "Ext.topic0.name_0" not in text:
                    self.assertNotIn("- `MathlibExt/A/M0`: 1\n", text)
                    self.assertNotIn("| `MathlibExt/A/M0` |", text)
                    self.assertNotIn("- `MathlibExt/Gone/M0`\n", text)

    def test_the_longest_list_gives_way_first(self) -> None:
        pointer = f"`python3 scripts/graph_batch.py verify {'c' * 40}`, run from a checkout of `main`, prints them all."
        plan = batch.PlacementPlan(added=[batch.Placement(f"MathlibExt/A/M{number}", "Algebra/groups", f"Topic {number}",
                                                          f"#{number}") for number in range(1500)])
        links = batch.LinkPlan(left=[("af_" + "3" * 24, "Algebra/a.md", "#7 adds 2 documented declarations in its topic "
                                      "that could state it", ["Ext.a", "Ext.b"]),
                                     ("af_" + "4" * 24, "Algebra/b.md", "#8 names it; its candidate is gone", [])])

        def report(modules: int) -> dict:
            return {"missing": [f"Ext.n{number}" for number in range(modules)],
                    "new": {f"Ext.n{number}": f"MathlibExt/A/M{number}" for number in range(modules)}}

        # The placements, the longest list, give way; then the description fits, and the rest stays.
        text = self.describe(plan, links, report(1000))
        self.assertTrue(f"### Placements\n\n1500 modules placed, too many to list here: {pointer}\n" in text)
        self.assertTrue("### New pages by module\n\n- `MathlibExt/A/M0`: 1\n" in text)
        self.assertTrue(f"- `af_{'3' * 24}` (`Algebra/a.md`): #7 adds 2 documented declarations in its topic that could "
                        "state it; given no page: `Ext.a`, `Ext.b`\n" in text)
        self.assertTrue(f"- `af_{'4' * 24}` (`Algebra/b.md`): #8 names it; its candidate is gone\n" in text)
        self.assertLess(len(text), batch.BODY_LIMIT)
        # With more new pages, their list gives way too.
        text = self.describe(plan, links, report(4000))
        self.assertTrue(f"### New pages by module\n\n4000 new pages, for declarations of 4000 modules, too many to list "
                        f"here: {pointer}\n" in text)
        self.assertTrue(f"### Placements\n\n1500 modules placed, too many to list here: {pointer}\n" in text)
        self.assertLess(len(text), batch.BODY_LIMIT)
        # verify prints every list in full.
        whole = self.describe(plan, links, report(4000), full=True)
        self.assertTrue("| `MathlibExt/A/M1499` | `Algebra/groups` | `Topic 1499` | #1499 |" in whole)
        self.assertTrue("- `MathlibExt/A/M3999`: 1" in whole)
        # The pages left for an editor give way last, and only to a line each, with how many declarations each gives no
        # page: their list is the only record of what the batch withholds, whose names verify prints.
        many = batch.LinkPlan(left=[("af_" + "3" * 24, "Algebra/a.md", "#7 adds 4000 documented declarations in its "
                                     "topic that could state it", [f"Ext.name_{number}" for number in range(4000)]),
                                    ("af_" + "4" * 24, "Algebra/b.md", "#8 names it; its candidate is gone", [])])
        text = self.describe(plan, many, report(1000))
        self.assertTrue(f"### Placements\n\n1500 modules placed, too many to list here: {pointer}\n" in text)
        self.assertTrue("and those counted here then get their pages only from such a batch ([Graph-sync batches]"
                        "(docs/BLUEPRINT.md#graph-sync-batches)). A line a page gives the pull requests that name it, the "
                        "short names of its reason and how many declarations it gives no page, too many to name here: "
                        f"{pointer}\n\n- `Algebra/a.md`, #7: several candidates in its topic; 4000 given no page\n"
                        "- `Algebra/b.md`, #8: its candidate is gone\n\n" in text)
        self.assertNotIn("Ext.name_0", text)
        self.assertLess(len(text), batch.BODY_LIMIT)
        self.assertTrue("`Ext.name_0`, `Ext.name_1`, " in self.describe(plan, many, report(1000), full=True))
        # While another list can give way, they keep every name.
        some = batch.LinkPlan(left=[(f"af_{page:024x}", f"Algebra/p{page}.md", f"#{page} adds 30 documented declarations "
                                     "in its topic that could state it", [f"Ext.n{page}_{name}" for name in range(30)])
                                    for page in range(50)])
        dropped = batch.PlacementPlan(dropped=[f"MathlibExt/Gone/LongModuleName{number}" for number in range(1500)])
        self.assertGreater(len(self.describe(dropped, some, full=True)), batch.BODY_LIMIT)
        text = self.describe(dropped, some)
        self.assertTrue(f"### Placements dropped\n\n1500 placements dropped, too many to list here: {pointer}\n" in text)
        self.assertTrue("; given no page: `Ext.n0_0`, `Ext.n0_1`, " in text and "`Ext.n49_29`\n" in text)
        self.assertLess(len(text), batch.BODY_LIMIT)


class LinkedRows(unittest.TestCase):
    def test_a_linked_row_keeps_its_subject_id_and_origin(self) -> None:
        seed = {"source": "mathgraph", "node": "mg_1", "revision": "r"}
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/a.md"}], "id": "af_" + "a" * 24,
               "extensions": {"org.atlas-wiki": {"kind": "theorem", "seed": seed,
                                                 "counterpart": [{"mathlib": "Nat.Prime", "relation": "variant"}]}}}
        linked = batch.linked_row(row, "Ext.a")
        # The Lean link right after the id, as the sync writes a row; the kind and the counterparts go.
        self.assertEqual(json.dumps(linked), json.dumps({
            "subject": row["subject"], "id": row["id"], "object": [{"location": {"declaration": "Ext.a"}}],
            "extensions": {"org.atlas-wiki": {"seed": seed}}}))
        self.assertEqual(row["extensions"]["org.atlas-wiki"]["kind"], "theorem")
        bare = batch.linked_row({"subject": row["subject"], "id": row["id"],
                                 "extensions": {"org.atlas-wiki": {"kind": "def"}}}, "Ext.a")
        self.assertEqual(list(bare), ["subject", "id", "object"])

    def test_the_links_of_a_pages_own_dependency_sections(self) -> None:
        text = ("# A\n\nSee [B](b.md).\n\n## Depends on\n\n- [C](c.md)\n- [D](../d.md)\n\n## Proof depends on\n\n"
                "- [E](e.md)\n\n## Informally uses\n\n- [F](f.md)\n\n## Sources\n\n- [A book](https://example.org/a)\n")
        self.assertEqual(batch.own_prerequisites(text), (["c.md", "../d.md"], ["e.md"]))
        self.assertEqual(batch.own_prerequisites("# A\n\nNo sections.\n"), ([], []))
        # As Autoform reads them: a heading in another case, a reference link and a titled one; not a code block.
        text = ("# A\n\n## DEPENDS ON\n\n- [C][c]\n- [D](d.md \"D\")\n\n```\n[E](e.md)\n```\n\n[c]: c.md\n")
        self.assertEqual(batch.own_prerequisites(text), (["c.md", "d.md"], []))
        self.assertIsNone(batch.own_prerequisites("No title.\n\n## Depends on\n\n- [C](c.md)\n"))

    def test_a_kind_that_is_no_kind(self) -> None:
        for kind in (["theorem"], {"a": 1}, 3, None, "Theorem", "theorem_wanted"):
            with self.subTest(kind=kind):
                self.assertIsNone(batch.recorded_kind({"extensions": {"org.atlas-wiki": {"kind": kind}}}))
        self.assertIsNone(batch.recorded_kind({"extensions": ["x"]}))
        self.assertIsNone(batch.recorded_kind({"extensions": {"org.atlas-wiki": "x"}}))
        self.assertEqual(batch.recorded_kind({"extensions": {"org.atlas-wiki": {"kind": "lemma"}}}), "lemma")

    def test_no_row_when_the_defaults_credit_otherwise(self) -> None:
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/a.md"}], "id": "af_" + "a" * 24}
        with patch.object(batch.sync, "crediting", return_value=None):
            self.assertIsNone(batch.linked_row(row, "Ext.a"))


TAXONOMY = {"schema": "atlas-wiki-taxonomy/v1", "regions": {"Algebra & Number Theory": ["Algebra"]},
            "subjects": {"Algebra": {"title": "Algebra", "description": "Operations.", "fields": [
                {"slug": "groups", "title": "Groups", "description": "Groups.", "subfields": []},
                {"slug": "rings", "title": "Rings", "description": "Rings.", "subfields": []}]}},
            "placements": {"MathlibExt/Algebra/Groups": {"to": "Algebra/groups", "title": "Group basics"},
                           "WantedExt/Algebra/SylowWanted": {"to": "Algebra/groups", "title": "Sylow theorems"}},
            "mathlib_exclusions": {}}
PAGES = {"README.md": "# ATLAS roadmap\n\n## Algebra & Number Theory\n\n- [Algebra](Algebra/README.md)\n",
         "Algebra/README.md": "# Algebra\n\nOperations.\n\n- [Groups](groups/README.md)\n- [Rings](rings/README.md)\n",
         "Algebra/groups/README.md": "# Groups\n\nGroups.\n\n- [Group basics](group-basics/README.md)\n"
                                     "- [Sylow theorems](sylow-theorems/README.md)\n",
         "Algebra/groups/group-basics/README.md": "# Group basics\n\n- [Lagrange](lagrange.md)\n",
         "Algebra/groups/group-basics/lagrange.md": "# Lagrange\n\nThe order of a subgroup divides the order of the group.\n",
         "Algebra/groups/sylow-theorems/README.md": "# Sylow theorems\n\n- [Sylow](sylow.md)\n",
         "Algebra/groups/sylow-theorems/sylow.md": "# Sylow\n\nSylow subgroups exist.\n",
         "Algebra/rings/README.md": "# Rings\n\nRings.\n"}
DECLARATIONS = {"Algebra/groups/group-basics/lagrange.md": "Ext.lagrange", "Algebra/groups/sylow-theorems/sylow.md": "Ext.sylow"}
LEAN = {"MathlibExt/Algebra/Groups.lean": "namespace Ext\n\n/-- The order of a subgroup divides the order of the group. -/\n"
                                         "theorem lagrange : True := trivial\n\nend Ext\n",
        "WantedExt/Algebra/SylowWanted.lean": "namespace Ext\n\n/-- Sylow subgroups exist. -/\ntheorem sylow : True := "
                                              "trivial\n\n/-- Sylow subgroups are conjugate. -/\ntheorem sylow_conj : True := "
                                              "trivial\n\nend Ext\n"}


@unittest.skipUnless(shutil.which("git"), "git is not installed")
class Batches(unittest.TestCase):
    """make, verify and base on a repository whose main merges pull requests as the merge queue does."""

    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.root, True)
        for name in ("graph_batch.py", "sync_wiki.py", "generate_wiki.py", "extract_v2_lean_dependencies.py"):
            self.write(f"scripts/{name}", (SCRIPTS / name).read_text())
        self.write("mkdocs.yml", (ROOT / "mkdocs.yml").read_text())
        self.write(".gitignore", "__pycache__/\n")
        self.write("scripts/taxonomy.json", self.taxonomy_text(TAXONOMY))
        for path, text in LEAN.items():
            self.write(path, text)
        rows = []
        for number, (page, text) in enumerate(PAGES.items(), 1):
            self.write(f"blueprint/roadmap/{page}", text)
            row = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}], "id": f"af_{number:024x}"}
            if page in DECLARATIONS:
                row["object"] = [{"location": {"declaration": DECLARATIONS[page]}}]
            rows.append(row)
        self.write("blueprint/links/roadmap.jsonl", json.dumps(rows[0]) + "\n")
        self.write("blueprint/links/Algebra.jsonl", "".join(json.dumps(row) + "\n" for row in rows[1:]))
        self.write("blueprint/links/_defaults.json", json.dumps(sync.DEFAULTS) + "\n")
        self.write("scripts/wiki-sync.json", json.dumps({"docstrings": {
            "Ext.lagrange": sync.digest("The order of a subgroup divides the order of the group."),
            "Ext.sylow": sync.digest("Sylow subgroups exist.")}}, indent=0) + "\n")
        self.git("init", "-q", "-b", "main")
        # The batch commit takes the identity of whoever runs make, as any commit does.
        self.git("config", "user.name", "Batch maker")
        self.git("config", "user.email", "batch@example.invalid")
        self.base = self.commit("base")
        self.bodies: dict[str, str] = {}

    @staticmethod
    def taxonomy_text(taxonomy: dict) -> str:
        """The taxonomy as the repository writes it: one placement per line."""
        placements = ",\n".join(f"  {json.dumps(key)}: {json.dumps(value)}" for key, value in taxonomy["placements"].items())
        rest = {key: value for key, value in taxonomy.items() if key != "placements"}
        head = json.dumps({key: rest[key] for key in ("schema", "regions", "subjects")}, indent=1)[:-2]
        return f"{head},\n \"placements\": {{\n{placements}\n }},\n \"mathlib_exclusions\": {{}}\n}}\n"

    def write(self, path: str, text: str) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD")

    def merge(self, number: int, change, body: str = "Graph: new\n") -> str:
        """Merge a pull request whose branch makes *change*, as the merge queue does: a merge commit on main."""
        self.git("switch", "-q", "-c", f"topic-{number}")
        change()
        self.commit(f"Pull request {number}")
        self.git("switch", "-q", "main")
        self.git("merge", "-q", "--no-ff", "-m", f"Merge pull request #{number} from someone/topic-{number}",
                 f"topic-{number}")
        self.bodies[str(number)] = body
        return self.git("rev-parse", "HEAD")

    def tool(self, *args: str, env: dict | None = None, from_batch: bool = False) -> subprocess.CompletedProcess:
        """Run the tool. verify runs from main, as a batch's reviewer runs it: with the batch at HEAD, from the commit
        it was made on, and back after (unless *from_batch*)."""
        bodies = self.root.parent / f"{self.root.name}-bodies.json"
        # A description given as plain lines comes with its rendering, as gh gives it.
        bodies.write_text(json.dumps({number: {"body": value, "html": rendered(value)} if isinstance(value, str)
                                      else value for number, value in self.bodies.items()}))
        self.addCleanup(bodies.unlink, True)
        extra = ["--bodies", str(bodies)] if args[0] in ("make", "verify") else []
        command = [sys.executable, str(self.root / "scripts" / "graph_batch.py"), *args, *extra]
        if args[0] == "verify" and not from_batch:
            named = [arg for arg in args[1:] if not arg.startswith("-") and not arg.startswith(str(self.root.parent))]
            target = self.git("rev-parse", named[0] if named else "HEAD")
            if target == self.git("rev-parse", "HEAD"):
                branch = self.git("rev-parse", "--abbrev-ref", "HEAD")
                self.git("switch", "-q", "--detach", "HEAD^")
                try:
                    command = [sys.executable, str(self.root / "scripts" / "graph_batch.py"), "verify", target,
                               *[arg for arg in args[1:] if arg not in named], *extra]
                    return subprocess.run(command, cwd=self.root, capture_output=True, text=True, env=env)
                finally:
                    self.git("switch", "-q", branch) if branch != "HEAD" else self.git("switch", "-q", "--detach",
                                                                                         target)
        return subprocess.run(command, cwd=self.root, capture_output=True, text=True, env=env)

    def land(self, number: int, branch: str) -> None:
        """Land the batch at HEAD as pull request *number*, as the merge queue does, and go back to main."""
        self.git("switch", "-q", "-c", branch)
        self.git("switch", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^")
        self.git("merge", "-q", "--no-ff", "-m", f"Merge pull request #{number} from someone/{branch}", branch)
        self.bodies[str(number)] = "Graph: batch\n"

    def module(self, path: str, names: list[str], heading: str = "") -> None:
        """A module of documented theorems *names*, with a `# heading` in its module docstring when given."""
        self.write(path, (f"/-!\n# {heading}\n-/\n\n" if heading else "") + "namespace Ext\n\n" + "".join(
            f"/-- {name} holds. -/\ntheorem {name} : True := trivial\n\n" for name in names) + "end Ext\n")

    def cosets(self) -> None:
        self.write("MathlibExt/Algebra/Groups.lean", LEAN["MathlibExt/Algebra/Groups.lean"].replace(
            "end Ext", "/-- Cosets partition the group. -/\ntheorem cosets : True := trivial\n\nend Ext"))

    def add(self, path: str, name: str) -> None:
        """One more documented theorem, *name*, at the end of the module at *path*."""
        target = self.root / path
        target.write_text(target.read_text().replace(
            "end Ext", f"/-- {name} holds. -/\ntheorem {name} : True := trivial\n\nend Ext"))

    def add_text(self, path: str, text: str) -> None:
        """*text* at the end of the module at *path*."""
        target = self.root / path
        target.write_text(target.read_text().replace("end Ext", f"{text}\n\nend Ext"))

    def remove(self, path: str, name: str) -> None:
        """Take the documented theorem *name* that add wrote out of the module at *path*."""
        target = self.root / path
        target.write_text(target.read_text().replace(f"/-- {name} holds. -/\ntheorem {name} : True := trivial\n\n", ""))

    def planned(self, page: str, article: str, extensions: dict | None = None, depends: bool | str = False,
                listed: bool = True, proof: str | None = None) -> None:
        """A planned page at *page*, listed on its folder page unless not *listed*, whose row has the article id
        *article* and *extensions* (a theorem's kind by default), with a `## Depends on` section when *depends*: a link
        to the linked page of Sylow's theorem, or to *depends* when it names a page."""
        folder, name = page.rsplit("/", 1)
        title = name.removesuffix(".md").replace("-", " ").capitalize()
        target = depends if isinstance(depends, str) else "../sylow-theorems/sylow.md"
        self.write(f"blueprint/roadmap/{page}", f"# {title}\n\n{title} holds.\n"
                   + (f"\n## Depends on\n\n- [Prerequisite]({target})\n" if depends else "")
                   + (f"\n## Proof depends on\n\n- [Proof prerequisite]({proof})\n" if proof else "")
                   + "\n## Sources\n\n- A book.\n")
        readme = self.root / "blueprint/roadmap" / folder / "README.md"
        if listed:
            readme.write_text(readme.read_text() + f"- [{title}]({name})\n")
        row = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}], "id": article,
               "extensions": extensions if extensions is not None else {"org.atlas-wiki": {"kind": "theorem"}}}
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps(row) + "\n")

    def rows(self) -> dict[str, dict]:
        """The rows of the Algebra links file, by article id."""
        return {row["id"]: row for row in map(json.loads, (self.root / "blueprint/links/Algebra.jsonl").read_text()
                                                .splitlines())}

    def description(self, *args: str) -> str:
        """The description make writes, which must succeed, given *args*."""
        body = self.root.parent / f"{self.root.name}-body.md"
        self.addCleanup(body.unlink, True)
        result = self.tool("make", *args, "--body", str(body))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return body.read_text()

    def placements(self) -> dict:
        return json.loads((self.root / "scripts/taxonomy.json").read_text())["placements"]

    def lean_only_merges(self) -> None:
        # A new documented module that nothing places; a proof that moves a wanted statement, with its name, into a new
        # module, whose Place: line names the wanted module's field but no topic; a second one that takes the wanted
        # module's last declaration and deletes it, with no Place: line; and a new module that its Place: line places,
        # beside a line about a module the pull request does not change.
        self.merge(1, lambda: self.write("MathlibExt/Algebra/Fields.lean", "namespace Ext\n\n/-- Fields are rings. -/\n"
                                         "theorem fields : True := trivial\n\n/-- Fields have no zero divisors. -/\n"
                                         "theorem fields_domain : True := trivial\n\nend Ext\n"))
        self.merge(2, lambda: (self.write("MathlibExt/Algebra/Sylow.lean", "namespace Ext\n\n/-- Sylow subgroups exist. -/\n"
                                          "theorem sylow : True := trivial\n\n/-- Sylow counting. -/\ntheorem sylow_count : True "
                                          ":= trivial\n\nend Ext\n"),
                               self.write("WantedExt/Algebra/SylowWanted.lean", "namespace Ext\n\n/-- Sylow subgroups are "
                                          "conjugate. -/\ntheorem sylow_conj : True := trivial\n\nend Ext\n")),
                   "Graph: new\nPlace: MathlibExt/Algebra/Sylow -> Algebra/groups\n")
        self.merge(3, lambda: (self.write("MathlibExt/Algebra/SylowConj.lean", "namespace Ext\n\n/-- Sylow subgroups are "
                                          "conjugate. -/\ntheorem sylow_conj : True := trivial\n\n/-- Conjugates of a Sylow "
                                          "subgroup are Sylow. -/\ntheorem sylow_conj_sylow : True := trivial\n\nend Ext\n"),
                               (self.root / "WantedExt/Algebra/SylowWanted.lean").unlink()))
        self.merge(4, lambda: self.write("MathlibExt/Algebra/Units.lean", "/-!\n# Units of a ring\n-/\n\nnamespace Ext\n\n"
                                         "/-- Units form a group. -/\ntheorem units : True := trivial\n\n/-- Units are not "
                                         "zero. -/\ntheorem units_ne_zero : True := trivial\n\nend Ext\n"),
                   "Graph: new\nPlace: MathlibExt/Algebra/Units -> Algebra/rings\n"
                   "Place: MathlibExt/Algebra/Fields -> Algebra/rings | Not mine\n")

    def test_a_batch_places_syncs_and_checks_what_main_merged(self) -> None:
        self.lean_only_merges()
        head = self.git("rev-parse", "HEAD")
        body = self.root.parent / f"{self.root.name}-body.md"
        self.addCleanup(body.unlink, True)
        result = self.tool("make", "--base", self.base, "--body", str(body))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        commit = self.git("rev-parse", "HEAD")
        self.assertEqual(self.git("rev-parse", "HEAD^"), head)
        message = self.git("log", "-1", "--format=%B")
        self.assertIn(f"Graph-sync-base: {self.base}\nGraph-sync-through: {head}", message)
        changed = self.git("diff", "--name-only", head, commit).splitlines()
        self.assertTrue(all(batch.batch_path(path) for path in changed), changed)
        placements = json.loads((self.root / "scripts/taxonomy.json").read_text())["placements"]
        # The proofs' modules take their wanted statements' place and topic, the deleted module loses its own, the
        # Place: line places its own module, with its heading as topic, and not another pull request's, and the module
        # nothing places stays unplaced.
        self.assertEqual(placements["MathlibExt/Algebra/Sylow"], {"to": "Algebra/groups", "title": "Sylow theorems"})
        self.assertEqual(placements["MathlibExt/Algebra/SylowConj"], {"to": "Algebra/groups", "title": "Sylow theorems"})
        self.assertNotIn("WantedExt/Algebra/SylowWanted", placements)
        self.assertEqual(placements["MathlibExt/Algebra/Units"], {"to": "Algebra/rings", "title": "Units of a ring"})
        self.assertNotIn("MathlibExt/Algebra/Fields", placements)
        roadmap = self.root / "blueprint/roadmap"
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/groups/sylow-theorems").iterdir()),
                         ["README.md", "sylow-conj-sylow.md", "sylow-count.md", "sylow.md"])
        self.assertIn("sylow-count.md", (roadmap / "Algebra/groups/sylow-theorems/README.md").read_text())
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/rings/units-of-a-ring").iterdir()),
                         ["README.md", "units-ne-zero.md", "units.md"])
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/not-yet-classified/fields").iterdir()),
                         ["README.md", "fields-domain.md", "fields.md"])
        text = body.read_text()
        self.assertTrue(text.startswith("Graph: batch\n"), text)
        self.assertIn("| `MathlibExt/Algebra/Sylow` | `Algebra/groups` | `Sylow theorems` | #2 |", text)
        self.assertIn("| `MathlibExt/Algebra/SylowConj` | `Algebra/groups` | `Sylow theorems` | "
                      "WantedExt/Algebra/SylowWanted |", text)
        self.assertIn("| `MathlibExt/Algebra/Units` | `Algebra/rings` | `Units of a ring` | #4 |", text)
        self.assertIn("#4: `MathlibExt/Algebra/Fields` is left unplaced: the pull request's merge does not change it",
                      text)
        self.assertIn("- `WantedExt/Algebra/SylowWanted`", text)
        self.assertIn("### New modules left unplaced", text)
        self.assertIn("- `MathlibExt/Algebra/Fields`: in `Algebra/not-yet-classified/`", text)
        # make shows the sync's own report.
        self.assertIn(dict(sync.REPORT)["added"], result.stdout)
        # verify agrees, run from main; run from the batch itself, it refuses.
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.tool("verify", commit, from_batch=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("run verify from an up-to-date checkout of main, not from the batch itself", result.stderr)
        # base names the batch once it has merged.
        self.assertEqual(self.tool("base").returncode, 1)
        self.land(5, "batch-1")
        result = self.tool("base")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(f"Last batch: {commit}, from {self.base} up to {head}.", result.stdout)
        self.assertIn(f"The next batch starts from {head}.", result.stdout)

    def test_the_next_batch_starts_where_the_last_one_ended(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        first = self.git("rev-parse", "HEAD")
        # The batch lands as a pull request, then main merges more Lean.
        self.git("switch", "-q", "-c", "batch-1")
        self.git("switch", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #5 from someone/batch-1", "batch-1")
        self.bodies["5"] = "Graph: batch\n"
        self.merge(6, self.cosets)
        result = self.tool("make")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        message = self.git("log", "-1", "--format=%B")
        self.assertIn(f"Graph-sync-base: {self.git('rev-parse', first + '^')}", message)
        changed = self.git("diff", "--name-only", "HEAD^", "HEAD").splitlines()
        self.assertEqual(sorted(changed), ["blueprint/links/Algebra.jsonl",
                                           "blueprint/roadmap/Algebra/groups/group-basics/README.md",
                                           "blueprint/roadmap/Algebra/groups/group-basics/cosets.md",
                                           "scripts/wiki-sync.json"])
        # Nothing more to do on a main the batch has caught up with.
        self.git("switch", "-q", "-c", "batch-2")
        self.git("switch", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #7 from someone/batch-2", "batch-2")
        self.merge(8, lambda: self.write("README.md", "Docs.\n"))
        result = self.tool("make")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Nothing to sync", result.stdout)
        self.assertEqual(self.git("log", "-1", "--format=%s"), "Merge pull request #8 from someone/topic-8")

    def test_verify_refuses_a_batch_that_is_not_exactly_the_tools(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        message = self.git("log", "-1", "--format=%B")
        # A page edited by hand after the run.
        page = self.root / "blueprint/roadmap/Algebra/not-yet-classified/fields/fields.md"
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.git("commit", "-q", "-a", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("does not find the batch's wiki exactly the sync's", result.stderr)
        # A placement the plan does not make.
        self.git("reset", "-q", "--hard", "HEAD^")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        taxonomy = self.root / "scripts/taxonomy.json"
        taxonomy.write_text(taxonomy.read_text().replace('"title": "Units of a ring"', '"title": "Unit groups"'))
        self.git("commit", "-q", "-a", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("not main's with the placement plan applied: the entries of MathlibExt/Algebra/Units differ",
                      result.stderr)
        # A commit that changes a file a batch never changes is no batch.
        self.write("README.md", "Docs.\n")
        self.git("add", "README.md")
        self.git("commit", "-q", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not a batch", result.stderr)

    def test_verify_from_a_newer_main_checks_the_merge(self) -> None:
        self.lean_only_merges()
        through = self.git("rev-parse", "HEAD")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        commit = self.git("rev-parse", "HEAD")
        self.git("branch", "batch", commit)

        def main_merges(number: int, change) -> None:
            self.git("reset", "-q", "--hard", through)
            self.merge(number, change)

        # A Lean pull request merged after the batch was made: it still merges, and nothing breaks.
        main_merges(9, lambda: self.write("MathlibExt/Algebra/Other.lean", "namespace Ext\n\n/-- Other. -/\n"
                                          "theorem other : True := trivial\n\nend Ext\n"))
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merges cleanly into", result.stdout)

        # A graph pull request that gave one of the batch's declarations a page of its own: two pages for one
        # declaration once both merge, which the check finds though the files merge cleanly.
        def hand_page() -> None:
            self.write("blueprint/roadmap/Algebra/groups/group-basics/fields-by-hand.md", "# Fields\n\nFields are rings.\n")
            readme = self.root / "blueprint/roadmap/Algebra/groups/group-basics/README.md"
            readme.write_text(readme.read_text() + "- [Fields](fields-by-hand.md)\n")
            # Its row among the others in path order, as the sync puts one, away from the rows the batch adds.
            links = self.root / "blueprint/links/Algebra.jsonl"
            lines = links.read_text().splitlines(keepends=True)
            lines.insert(3, json.dumps({
                "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/fields-by-hand.md"}],
                "id": "af_" + "e" * 24, "object": [{"location": {"declaration": "Ext.fields"}}]}) + "\n")
            links.write_text("".join(lines))

        main_merges(10, hand_page)
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("the batch breaks what the scoped check reads", result.stderr)
        self.assertIn("Ext.fields", result.stderr)

        # A change to a folder page the batch also extends: no clean merge.
        main_merges(11, lambda: self.write("blueprint/roadmap/Algebra/README.md",
                                           PAGES["Algebra/README.md"] + "- [Fields](fields/README.md)\n"))
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("no longer merges cleanly", result.stderr)

        # A graph pull request that placed a module the batch places too, on another line: the files merge cleanly,
        # but the taxonomy would place the module twice.
        def place_units() -> None:
            taxonomy = self.root / "scripts/taxonomy.json"
            taxonomy.write_text(taxonomy.read_text().replace(
                ' "placements": {\n',
                ' "placements": {\n  "MathlibExt/Algebra/Units": {"to": "Algebra/rings", "title": "Units"},\n'))

        main_merges(12, place_units)
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("leaves scripts/taxonomy.json unreadable", result.stderr)

        # A newer main whose check stops before it writes a report, as on a git error: the batch's own check passed and
        # wrote one, but that report is never read as the merge's.
        def stop_the_check() -> None:
            path = self.root / "scripts/sync_wiki.py"
            path.write_text(path.read_text().replace(
                'if __name__ == "__main__":', 'if __name__ == "__main__" and "--check" in sys.argv:\n    sys.exit(2)\n\n'
                'if __name__ == "__main__":', 1))

        main_merges(13, stop_the_check)
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("the batch could not be checked: the scoped check stopped (exit 2)", result.stderr)

    def test_verify_prints_what_the_reviewer_reads(self) -> None:
        # A Lean pull request edits the docstring of a declaration that has a page, and adds one more declaration:
        # the batch writes the new digest, so the page must be named for the reviewer to check.
        self.merge(1, lambda: self.write("MathlibExt/Algebra/Groups.lean", LEAN["MathlibExt/Algebra/Groups.lean"]
                                         .replace("divides the order of the group.", "divides the order of the finite "
                                                  "group.").replace("end Ext", "/-- Cosets partition the group. -/\n"
                                                                    "theorem cosets : True := trivial\n\nend Ext")))
        made = self.description("--base", self.base)
        commit = self.git("rev-parse", "HEAD")
        written = self.root.parent / f"{self.root.name}-verify-body.md"
        self.addCleanup(written.unlink, True)
        result = self.tool("verify", commit, "--body", str(written))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("read this, not the pull request's description", result.stdout)
        self.assertIn("### Pages to check", result.stdout)
        self.assertIn("Ext.lagrange (Algebra/groups/group-basics/lagrange.md)", result.stdout)
        self.assertIn("- 1 new pages, for declarations of 1 modules; 1 folder pages written or extended", result.stdout)
        # What it writes is exactly what make wrote.
        self.assertEqual(written.read_text(), made)

    def test_make_needs_a_clean_checkout_and_an_older_base(self) -> None:
        self.lean_only_merges()
        self.write("MathlibExt/Algebra/Fields.lean", "-- edited\n")
        result = self.tool("make", "--base", self.base)
        self.assertEqual(result.returncode, 1)
        self.assertIn("needs a clean checkout", result.stderr)
        self.git("checkout", "--", ".")
        result = self.tool("make")
        self.assertEqual(result.returncode, 1)
        self.assertIn("give the first batch's base with --base", result.stderr)
        result = self.tool("make", "--base", "HEAD")
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not an older commit", result.stderr)

    def test_make_without_gh_says_so(self) -> None:
        self.lean_only_merges()
        tools = self.root.parent / f"{self.root.name}-bin"
        tools.mkdir()
        self.addCleanup(shutil.rmtree, tools, True)
        (tools / "git").symlink_to(shutil.which("git"))
        result = subprocess.run([sys.executable, str(self.root / "scripts" / "graph_batch.py"), "make", "--base",
                                 self.base], cwd=self.root, capture_output=True, text=True,
                                env={**os.environ, "PATH": str(tools)})
        self.assertEqual(result.returncode, 1)
        self.assertIn("needs `gh`", result.stderr)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_verify_needs_no_configured_identity(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        self.git("config", "--unset", "user.name")
        self.git("config", "--unset", "user.email")
        home = self.root.parent / f"{self.root.name}-home"
        home.mkdir()
        self.addCleanup(shutil.rmtree, home, True)
        environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        environment.update(HOME=str(home), XDG_CONFIG_HOME=str(home), GIT_CONFIG_NOSYSTEM="1")
        result = self.tool("verify", env=environment)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_verify_runs_only_what_main_had(self) -> None:
        # A pull request whose first commit changes the sync and whose second puts it back: main merges it, but never
        # had the first commit's tree, which no one checked.
        marker = self.root.parent / f"{self.root.name}-ran"
        self.addCleanup(marker.unlink, True)
        sync_path = self.root / "scripts/sync_wiki.py"
        original = sync_path.read_text()
        self.git("switch", "-q", "-c", "topic-1")
        sync_path.write_text(original.replace('if __name__ == "__main__":',
                                              f"open({str(marker)!r}, 'w').write('ran')\n\nif __name__ == \"__main__\":"))
        self.git("commit", "-q", "-am", "Work in progress")
        unmerged = self.git("rev-parse", "HEAD")
        sync_path.write_text(original)
        self.write("README.md", "Docs.\n")
        self.commit("Finish")
        self.git("switch", "-q", "main")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #1 from someone/topic-1", "topic-1")
        self.bodies["1"] = "Graph: none\n"
        # A commit shaped as a batch on that branch commit is none, and its sync never runs.
        self.git("switch", "-q", "--detach", unmerged)
        self.write("scripts/wiki-sync.json", (self.root / "scripts/wiki-sync.json").read_text() + "\n")
        self.git("commit", "-q", "-am", f"{batch.SUBJECT}{unmerged[:12]}\n\nGraph-sync-base: {self.base}\n"
                                        f"Graph-sync-through: {unmerged}\n")
        crafted = self.git("rev-parse", "HEAD")
        self.git("switch", "-q", "main")
        result = self.tool("verify", crafted)
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not a batch", result.stderr)
        self.assertFalse(marker.exists())
        # Nor is a commit that changes nothing.
        main = self.git("rev-parse", "HEAD")
        self.git("commit", "-q", "--allow-empty", "-m", f"{batch.SUBJECT}{main[:12]}\n\nGraph-sync-base: {self.base}\n"
                                                        f"Graph-sync-through: {main}\n")
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not a batch", result.stderr)

    def test_batches_skip_no_lean(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        through = self.git("rev-parse", "HEAD^")
        self.land(5, "batch-1")
        self.merge(6, self.cosets)
        after = self.git("rev-parse", "HEAD")
        self.merge(7, lambda: self.write("README.md", "Docs.\n"))
        # make refuses to start after where the last batch ended.
        result = self.tool("make", "--base", after)
        self.assertEqual(result.returncode, 1)
        self.assertIn("would skip the Lean merged in between", result.stderr)
        # A graph pull request whose commit copies the trailers is no batch: the next batch still starts where the
        # last one ended.
        self.git("switch", "-q", "-c", "topic-8")
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        page.write_text(page.read_text() + "\nA remark.\n")
        self.git("commit", "-q", "-am", f"Edit a page\n\nGraph-sync-base: {self.base}\n"
                                        f"Graph-sync-through: {self.git('rev-parse', 'main')}\n")
        self.git("switch", "-q", "main")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #8 from someone/topic-8", "topic-8")
        self.bodies["8"] = "Graph: none\n"
        self.assertIn(f"The next batch starts from {through}.", self.tool("base").stdout)
        # verify refuses a batch whose base is after it.
        self.assertEqual(self.tool("make").returncode, 0)
        message = self.git("log", "-1", "--format=%B")
        self.git("commit", "-q", "--amend", "-m", message.replace(f"Graph-sync-base: {through}",
                                                                  f"Graph-sync-base: {after}"))
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("skips the Lean merged in between", result.stderr)
        # An earlier base does no harm: what the last batch wrote is not written again.
        self.git("reset", "-q", "--hard", "HEAD^")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        self.assertEqual(sorted(self.git("diff", "--name-only", "HEAD^", "HEAD").splitlines()),
                         ["blueprint/links/Algebra.jsonl", "blueprint/roadmap/Algebra/groups/group-basics/README.md",
                          "blueprint/roadmap/Algebra/groups/group-basics/cosets.md", "scripts/wiki-sync.json"])
        result = self.tool("verify")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_a_placement_keeps_a_modules_pages_together(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        self.land(5, "batch-1")
        # A later pull request adds to Fields, whose pages the first batch wrote in not-yet-classified/, and places it.
        fields = self.root / "MathlibExt/Algebra/Fields.lean"
        self.merge(6, lambda: fields.write_text(fields.read_text().replace(
            "end Ext", "/-- Fields are commutative. -/\ntheorem fields_comm : True := trivial\n\nend Ext")),
                   "Graph: new\nPlace: MathlibExt/Algebra/Fields -> Algebra/rings\n")
        text = self.description()
        self.assertNotIn("MathlibExt/Algebra/Fields", self.placements())
        self.assertTrue((self.root / "blueprint/roadmap/Algebra/not-yet-classified/fields/fields-comm.md").is_file())
        self.assertIn("`MathlibExt/Algebra/Fields` is left unplaced: it already has pages outside the topic `Fields` of "
                      "`Algebra/rings`", text)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_a_placement_keeps_a_modules_pages_in_their_topic(self) -> None:
        # A proof moves the wanted `sylow`, whose page is in the topic Sylow theorems, into a new module and asks for
        # another topic of the same field: the module stays where its page is, unplaced, with a note.
        self.merge(1, lambda: (self.module("MathlibExt/Algebra/SylowNew.lean", ["sylow", "sylow_count"]),
                               self.write("WantedExt/Algebra/SylowWanted.lean", "namespace Ext\n\n/-- Sylow subgroups "
                                          "are conjugate. -/\ntheorem sylow_conj : True := trivial\n\nend Ext\n")),
                   "Graph: new\nPlace: MathlibExt/Algebra/SylowNew -> Algebra/groups | Sylow counting\n")
        text = self.description("--base", self.base)
        self.assertNotIn("MathlibExt/Algebra/SylowNew", self.placements())
        self.assertIn("`MathlibExt/Algebra/SylowNew` is left unplaced: it already has pages outside the topic `Sylow "
                      "counting` of `Algebra/groups`", text)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_only_a_merged_pull_requests_head_counts_as_a_batch(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        through = self.git("rev-parse", "HEAD^")
        self.land(5, "batch-1")
        self.merge(6, self.cosets)
        # A graph pull request of two commits, the first carrying make's whole message.
        parent = self.git("rev-parse", "HEAD")
        self.git("switch", "-q", "-c", "topic-7")
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        page.write_text(page.read_text() + "\nA remark.\n")
        self.git("commit", "-q", "-am", f"{batch.SUBJECT}{parent[:12]}\n\nGraph-sync-base: {through}\n"
                                        f"Graph-sync-through: {parent}\n")
        page.write_text(page.read_text() + "\nAnother remark.\n")
        self.git("commit", "-q", "-am", "Another remark")
        self.git("switch", "-q", "main")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #7 from someone/topic-7", "topic-7")
        self.bodies["7"] = "Graph: af_x\n"
        self.assertIn(f"The next batch starts from {through}.", self.tool("base").stdout)
        self.assertEqual(self.tool("make").returncode, 0)
        self.assertTrue((self.root / "blueprint/roadmap/Algebra/groups/group-basics/cosets.md").is_file())

    def test_the_placement_rules(self) -> None:
        # To start from: a placed folder, a placed module, an unplaced one, and an entry for Mathlib.
        taxonomy = json.loads((self.root / "scripts/taxonomy.json").read_text())
        taxonomy["placements"]["MathlibExt/Algebra/Folder"] = {"to": "Algebra/rings", "title": "Folder topic"}
        taxonomy["placements"]["MathlibExt/Algebra/Old"] = {"to": "Algebra/rings", "title": "Old topic"}
        taxonomy["placements"]["Mathlib/Algebra/Gone"] = {"to": "Algebra/rings", "title": "Mathlib gone"}
        (self.root / "scripts/taxonomy.json").write_text(self.taxonomy_text(taxonomy))
        self.module("MathlibExt/Algebra/Folder/Inner.lean", ["inner_one", "inner_two"])
        self.module("MathlibExt/Algebra/Old.lean", ["old_one"])
        self.module("MathlibExt/Algebra/Loose.lean", ["loose_one"])
        self.module("MathlibExt/Nowhere/Older.lean", ["older_one"])
        self.base = self.commit("more to start from")
        # Two pull requests change one module and ask for different topics.
        self.merge(1, lambda: self.module("MathlibExt/Algebra/Rule1.lean", ["r1"]),
                   "Place: MathlibExt/Algebra/Rule1 -> Algebra/rings\n")
        self.merge(2, lambda: self.module("MathlibExt/Algebra/Rule1.lean", ["r1", "r1b"]),
                   "Place: MathlibExt/Algebra/Rule1 -> Algebra/rings | Rule one, again\n")
        # A field the taxonomy lacks, and a topic the line may not carry.
        self.merge(3, lambda: (self.module("MathlibExt/Algebra/Rule3.lean", ["r3"]),
                               self.module("MathlibExt/Algebra/Rule3b.lean", ["r3b"])),
                   "Place: MathlibExt/Algebra/Rule3 -> Algebra/fields\n"
                   "Place: MathlibExt/Algebra/Rule3b -> Algebra/rings | Fixes #1, cc @octocat\n")
        # Declarations from a placed module and from an unplaced one.
        self.merge(4, lambda: (self.module("MathlibExt/Algebra/Rule4.lean", ["lagrange", "loose_one"]),
                               self.write("MathlibExt/Algebra/Groups.lean", "-- emptied\n"),
                               (self.root / "MathlibExt/Algebra/Loose.lean").unlink()))
        # The same line twice, for a module whose name says nothing of its topic.
        self.merge(5, lambda: self.module("MathlibExt/Algebra/Rule5/Basic.lean", ["r5"]),
                   "Place: MathlibExt/Algebra/Rule5/Basic -> Algebra/rings\n" * 2)
        # A module moved out of a placed folder, which is left with no file.
        self.merge(6, lambda: (self.module("MathlibExt/Algebra/Moved.lean", ["inner_one", "inner_two"]),
                               (self.root / "MathlibExt/Algebra/Folder/Inner.lean").unlink()))

        # A module moved, its old placement removed by the same pull request: the base's placement counts.
        def move_old() -> None:
            self.module("MathlibExt/Algebra/New.lean", ["old_one"])
            (self.root / "MathlibExt/Algebra/Old.lean").unlink()
            path = self.root / "scripts/taxonomy.json"
            path.write_text(path.read_text().replace(
                '  "MathlibExt/Algebra/Old": {"to": "Algebra/rings", "title": "Old topic"},\n', ""))

        self.merge(7, move_old)
        # A module in a folder with no subject, and an older one there that gains a declaration and asks for a place,
        # which would leave its older declaration with no page.
        self.merge(8, lambda: (self.module("MathlibExt/Nowhere/Thing.lean", ["thing"]),
                               self.module("MathlibExt/Nowhere/Older.lean", ["older_one", "older_two"])),
                   "Place: MathlibExt/Nowhere/Older -> Algebra/rings\n")
        # A description edited after the merge: its lines are left out.
        self.merge(9, lambda: self.module("MathlibExt/Algebra/Edited.lean", ["edited_one"]))
        self.bodies["9"] = {"body": "Place: MathlibExt/Algebra/Edited -> Algebra/rings\n", "edited": True}
        self.merge(12, lambda: self.module("MathlibExt/Algebra/Escaped.lean", ["escaped_one"]))
        self.bodies["12"] = {"body": "Place: MathlibExt/Algebra/Escaped -\\> Algebra/rings\n",
                             "html": '<p dir="auto">Place: MathlibExt/Algebra/Escaped -&gt; Algebra/rings</p>'}
        # A description given with no rendering places nothing.
        self.merge(11, lambda: self.module("MathlibExt/Algebra/NoHtml.lean", ["no_html_one"]))
        self.bodies["11"] = {"body": "Place: MathlibExt/Algebra/NoHtml -> Algebra/rings\n"}
        # A line the Markdown reader would take but GitHub shows inside a code block, beside one it shows as text.
        self.merge(10, lambda: (self.module("MathlibExt/Algebra/Coded.lean", ["coded_one"]),
                                self.module("MathlibExt/Algebra/Shown.lean", ["shown_one"])))
        self.bodies["10"] = {"body": "- item\n  ```\n  x\n```\nPlace: MathlibExt/Algebra/Coded -> Algebra/rings\n```\n\n"
                                     "Place: MathlibExt/Algebra/Shown -> Algebra/rings\n",
                             "html": '<ul dir="auto">\n<li>item\n<pre><code>x\n</code></pre>\n</li>\n</ul>\n<pre><code>'
                                     'Place: MathlibExt/Algebra/Coded -&gt; Algebra/rings\n</code></pre>\n<p dir="auto">'
                                     'Place: MathlibExt/Algebra/Shown -&gt; Algebra/rings</p>'}
        text = self.description("--base", self.base)
        placements = self.placements()
        self.assertEqual({key: value for key, value in placements.items() if key not in TAXONOMY["placements"]}, {
            "MathlibExt/Algebra/Shown": {"to": "Algebra/rings", "title": "Shown"},
            "MathlibExt/Algebra/Escaped": {"to": "Algebra/rings", "title": "Escaped"},
            "MathlibExt/Algebra/Rule5/Basic": {"to": "Algebra/rings", "title": "Rule5"},
            "MathlibExt/Algebra/Moved": {"to": "Algebra/rings", "title": "Folder topic"},
            "MathlibExt/Algebra/New": {"to": "Algebra/rings", "title": "Old topic"},
            "Mathlib/Algebra/Gone": {"to": "Algebra/rings", "title": "Mathlib gone"}})
        self.assertIn("`MathlibExt/Algebra/Rule1` is left unplaced: #1, #2 ask for different places", text)
        self.assertIn("#3: `MathlibExt/Algebra/Rule3` is left unplaced: its line names no field or subfield", text)
        self.assertIn("#3: a `Place:` line is left out: its topic is not one line", text)
        self.assertNotIn("octocat", text)
        self.assertNotIn("Fixes", text)
        self.assertIn("MathlibExt/Algebra/Rule4 is left unplaced: its declarations came from modules placed differently "
                      "or not at all (MathlibExt/Algebra/Groups, MathlibExt/Algebra/Loose)", text)
        self.assertIn("| `MathlibExt/Algebra/Rule5/Basic` | `Algebra/rings` | `Rule5` | #5 |", text)
        self.assertIn("| `MathlibExt/Algebra/Moved` | `Algebra/rings` | `Folder topic` | "
                      "MathlibExt/Algebra/Folder/Inner |", text)
        self.assertIn("- `MathlibExt/Algebra/Folder`", text)
        self.assertIn("- `MathlibExt/Nowhere/Thing`: **no pages**, as its folder has no subject", text)
        self.assertIn("### Changed modules with no pages", text)
        self.assertIn("- `MathlibExt/Nowhere/Older`", text)
        self.assertIn("`MathlibExt/Nowhere/Older` is left unplaced: it is older than the batch, in a folder with no "
                      "subject", text)
        self.assertIn("#9: its `Place:` lines are left out: its description was edited after the merge", text)
        self.assertIn("- `MathlibExt/Algebra/Edited`: in `Algebra/not-yet-classified/`", text)
        self.assertIn("#10: 1 `Place:` line(s) left out: GitHub does not show them as lines of plain text", text)
        self.assertIn("#11: its `Place:` lines are left out: its rendering is not known", text)
        self.assertIn("- `MathlibExt/Algebra/NoHtml`: in `Algebra/not-yet-classified/`", text)
        # A line written with an escape is read as GitHub shows it, with no note.
        self.assertEqual(placements["MathlibExt/Algebra/Escaped"], {"to": "Algebra/rings", "title": "Escaped"})
        self.assertNotIn("#12:", text)
        self.assertIn("- `MathlibExt/Algebra/Coded`: in `Algebra/not-yet-classified/`", text)
        self.assertIn("- `MathlibExt/Algebra/Rule1`: in `Algebra/not-yet-classified/`", text)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_the_planned_pages_graph_lines_name(self) -> None:
        a = {name: "af_" + digits * (24 // len(digits)) for name, digits in (
            ("one", "a"), ("several", "b"), ("two", "c"), ("node", "d"), ("edited", "e"), ("hidden", "1"), ("def", "2"),
            ("far", "3"), ("s1", "4"), ("s2", "5"), ("held", "6"), ("kindless", "7"), ("field", "8"), ("part", "9"),
            ("unlisted", "f0"), ("extra", "0f"), ("twice", "ab"), ("mixed", "cd"), ("listed", "dc"), ("gapped", "fe"),
            ("renamed", "ef"), ("wgap", "ac"), ("vanish", "ca"), ("kept", "bd"), ("pre", "db"), ("shouty", "ae"),
            ("fenced", "ea"), ("inst", "af"), ("bold", "fa"), ("dep", "b2"), ("proofdep", "b3"))}
        sylow, basics = "Algebra/groups/sylow-theorems", "Algebra/groups/group-basics"
        seed = {"source": "mathgraph", "node": "mg_1", "revision": "r"}
        self.planned(f"{sylow}/sylow-counting.md", a["one"], {"org.atlas-wiki": {
            "kind": "theorem", "seed": seed, "counterpart": [{"mathlib": "Nat.Prime", "relation": "variant"}]}})
        self.planned(f"{sylow}/sylow-several.md", a["several"])
        self.planned(f"{basics}/two-prs.md", a["two"])
        self.planned(f"{basics}/node.md", a["node"], {"org.atlas-wiki": {"kind": "theorem"},
                                                     "org.autoform": {"not_ready": True}})
        self.planned(f"{basics}/edited.md", a["edited"])
        self.planned(f"{basics}/hidden.md", a["hidden"])
        self.planned(f"{basics}/a-definition.md", a["def"], {"org.atlas-wiki": {"kind": "def"}})
        self.planned(f"{sylow}/far.md", a["far"])
        self.planned(f"{sylow}/shared-one.md", a["s1"])
        self.planned(f"{sylow}/shared-two.md", a["s2"])
        self.planned(f"{basics}/held.md", a["held"], {"org.atlas-wiki": {"held": {
            "declaration": "Ext.held_decl", "reason": "false", "issue": 1}}})
        self.planned(f"{sylow}/kindless.md", a["kindless"], {})
        self.planned("Algebra/groups/in-field.md", a["field"])
        self.write(f"blueprint/roadmap/{sylow}/part-01/README.md", "# Part 1\n\n")
        readme = self.root / "blueprint/roadmap" / sylow / "README.md"
        readme.write_text(readme.read_text() + "- [Part 1](part-01/README.md)\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({"subject": [{"type": "generic", "uri": (
            f"../roadmap/{sylow}/part-01/README.md")}], "id": "af_" + "c0" * 12}) + "\n")
        self.planned(f"{sylow}/part-01/in-part.md", a["part"])
        self.planned(f"{sylow}/unlisted.md", a["unlisted"], listed=False)
        self.planned(f"{sylow}/extra.md", a["extra"], {"org.atlas-wiki": {"kind": "theorem", "pending": []}})
        self.planned(f"{sylow}/twice.md", a["twice"])
        self.planned(f"{sylow}/mixed.md", a["mixed"])
        self.planned(f"{sylow}/gapped.md", a["gapped"], depends="sylow-several.md")
        self.planned(f"{sylow}/renamed.md", a["renamed"])
        # A page linked to a wanted statement, which records no proof, and a page whose proof needs it.
        self.write(f"blueprint/roadmap/{sylow}/pre-wanted.md", "# Pre wanted\n\nPre holds.\n")
        (self.root / "blueprint/roadmap" / sylow / "README.md").write_text(
            (self.root / "blueprint/roadmap" / sylow / "README.md").read_text() + "- [Pre wanted](pre-wanted.md)\n")
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": f"../roadmap/{sylow}/pre-wanted.md"}], "id": a["pre"],
            "object": [{"location": {"declaration": "Ext.pre_wanted"}}]}) + "\n")
        self.add_text("WantedExt/Algebra/SylowWanted.lean", "/-- Pre holds. -/\ntheorem_wanted pre_wanted : True")
        digests = json.loads((self.root / "scripts/wiki-sync.json").read_text())
        digests["docstrings"]["Ext.pre_wanted"] = sync.digest("Pre holds.")
        self.write("scripts/wiki-sync.json", json.dumps(digests, indent=0) + "\n")
        self.planned(f"{sylow}/wanted-gap.md", a["wgap"], proof="pre-wanted.md")
        self.planned(f"{sylow}/vanish.md", a["vanish"])
        self.planned(f"{sylow}/kept.md", a["kept"], {})
        # Dependency sections the sync's exact match would miss, or cut from inside a code block.
        self.planned(f"{sylow}/shouty.md", a["shouty"], depends=True)
        shouty = self.root / "blueprint/roadmap" / sylow / "shouty.md"
        shouty.write_text(shouty.read_text().replace("## Depends on", "## DEPENDS ON"))
        self.planned(f"{sylow}/fenced.md", a["fenced"])
        fenced = self.root / "blueprint/roadmap" / sylow / "fenced.md"
        fenced.write_text(fenced.read_text().replace("Fenced holds.\n", "Fenced holds.\n\n```\n## Depends on\n```\n\n"
                                                                          "More prose.\n"))
        self.planned(f"{sylow}/inst.md", a["inst"], {"org.atlas-wiki": {"kind": "instance"}})
        # Pages whose own `## Depends on`, or `## Proof depends on`, links a linked page, which the declaration's Lean
        # may not record.
        self.planned(f"{sylow}/dep.md", a["dep"], depends=True)
        self.planned(f"{sylow}/proof-dep.md", a["proofdep"], proof="sylow.md")
        groups, wanted = "MathlibExt/Algebra/Groups.lean", "WantedExt/Algebra/SylowWanted.lean"
        (self.root / groups).write_text((self.root / groups).read_text().replace(
            "end Ext", "theorem held_decl : True := trivial\n\nend Ext"))
        self.base = self.commit("planned pages")
        before = self.rows()
        # One documented declaration in the page's topic, which the module's placement gives: linked.
        self.merge(1, lambda: self.add(wanted, "count_one"), f"Graph: {a['one']}\n")
        # Two there, in a module a `Place:` line puts there: neither, and no page for either.
        self.merge(2, lambda: self.module("MathlibExt/Algebra/Several.lean", ["several_a", "several_b"]),
                   f"Graph: {a['several']} new\nPlace: MathlibExt/Algebra/Several -> Algebra/groups | Sylow theorems\n")
        # A page two pull requests name.
        self.merge(3, lambda: self.add(groups, "two_a"), f"Graph: {a['two']}\n")
        self.merge(4, lambda: self.add(groups, "two_b"), f"Graph: {a['two']}\n")
        # A linked page, a folder page and an id no row has: left as they are, and the pull request's declaration gets
        # its page.
        self.merge(5, lambda: self.module("MathlibExt/Algebra/RingFacts.lean", ["rings_thm"]),
                   f"Graph: af_{5:024x}, af_{3:024x}, af_{'f' * 24}, new\n"
                   "Place: MathlibExt/Algebra/RingFacts -> Algebra/rings\n")
        # A description edited after the merge, and a line GitHub shows in a `<details>`: left out, with a note, and
        # their declarations get their pages.
        self.merge(6, lambda: self.add(groups, "edited_thm"))
        self.bodies["6"] = {"body": f"Graph: {a['edited']}\n", "html": rendered(f"Graph: {a['edited']}\n"),
                            "edited": True}
        self.merge(7, lambda: self.add(groups, "hidden_thm"))
        self.bodies["7"] = {"body": f"<details>\n<summary>More</summary>\n\nGraph: {a['hidden']}\n\n</details>\n",
                            "html": f'<details><summary>More</summary>\n<p dir="auto">Graph: {a["hidden"]}</p>\n'
                                    "</details>"}
        # A theorem, for the page of a definition: no candidate, and the theorem gets its page.
        self.merge(8, lambda: self.add(groups, "mismatch_thm"), f"Graph: {a['def']}\n")
        # A declaration whose module is placed in another topic: no page.
        self.merge(9, lambda: self.module("MathlibExt/Algebra/Far.lean", ["far_thm"]),
                   f"Graph: {a['far']}\nPlace: MathlibExt/Algebra/Far -> Algebra/rings | Far results\n")
        # One declaration that may state either of two pages: neither.
        self.merge(10, lambda: self.add(wanted, "shared_thm"), f"Graph: {a['s1']} {a['s2']}\n")
        # Pages the batch does not link, as an editor's call: one that holds a declaration back, one that records no
        # kind, one its folder page does not list, and one whose row holds more than a kind and an origin.
        self.merge(11, lambda: self.add(groups, "held_fix"), f"Graph: {a['held']}\n")
        self.merge(12, lambda: self.add(wanted, "kindless_thm"), f"Graph: {a['kindless']}\n")
        self.merge(13, lambda: self.add(wanted, "unlisted_thm"), f"Graph: {a['unlisted']}\n")
        self.merge(14, lambda: self.add(wanted, "extra_thm"), f"Graph: {a['extra']}\n")
        # A page right in the field's folder is in no topic; one in a part of the topic's folder is in it.
        self.merge(15, lambda: self.add(groups, "field_thm"), f"Graph: {a['field']}\n")
        self.merge(16, lambda: self.add(wanted, "part_thm"), f"Graph: {a['part']}\n")
        # Two pull requests name a page, but one description was edited after its merge: the other one counts.
        self.merge(17, lambda: self.add(wanted, "twice_a"))
        self.bodies["17"] = {"body": f"Graph: {a['twice']}\n", "html": rendered(f"Graph: {a['twice']}\n"),
                             "edited": True}
        self.merge(18, lambda: self.add(wanted, "twice_b"), f"Graph: {a['twice']}\n")
        # A node still to expand, which an editor expands or links: its candidate is withheld.
        self.merge(19, lambda: self.add(groups, "node_thm"), f"Graph: {a['node']}\n")
        # One candidate in the page's topic and one elsewhere: the first is linked, and the other gets its page.
        self.merge(20, lambda: (self.add(wanted, "mixed_near"), self.add(groups, "mixed_far")), f"Graph: {a['mixed']}\n")
        # A `Graph:` line in a list, which GitHub shows in the list: left out, with a note.
        self.merge(21, lambda: self.add(groups, "listed_thm"))
        self.bodies["21"] = {"body": f"- Graph: {a['listed']}\n",
                             "html": f'<ul dir="auto">\n<li>Graph: {a["listed"]}</li>\n</ul>'}
        # A page whose own `## Depends on` links a planned page, which no Lean can record: not linked.
        self.merge(22, lambda: self.add(wanted, "gap_thm"), f"Graph: {a['gapped']}\n")
        # Two candidates as the merge added them, though later Lean takes one away: not linked.
        self.merge(23, lambda: (self.add(wanted, "ren_a"), self.add(wanted, "ren_b")), f"Graph: {a['renamed']}\n")
        self.merge(24, lambda: self.remove(wanted, "ren_b"))
        # A wanted statement for a page whose proof needs a page not proved yet: not linked.
        self.merge(25, lambda: self.add_text(wanted, "/-- wgap_stmt holds. -/\ntheorem_wanted wgap_stmt : True"),
                   f"Graph: {a['wgap']}\n")
        # The one candidate, renamed by a later pull request: not linked, and what it became gets no page.
        self.merge(26, lambda: self.add(wanted, "van_a"), f"Graph: {a['vanish']}\n")
        self.merge(27, lambda: (self.remove(wanted, "van_a"), self.add(wanted, "van_b")))
        # A pull request whose description is not known: a note, and its declaration gets its page.
        self.merge(28, lambda: self.add(groups, "nobody_thm"))
        del self.bodies["28"]
        # A page the batch may not link, named by a pull request with no candidate: left as it is.
        self.merge(29, lambda: self.add_text(groups, "theorem undocumented_thm : True := trivial"), f"Graph: {a['kept']}\n")
        self.merge(30, lambda: self.add(wanted, "shouty_thm"), f"Graph: {a['shouty']}\n")
        self.merge(31, lambda: self.add(wanted, "fenced_thm"), f"Graph: {a['fenced']}\n")
        # A page of an instance, which gets no page: a definition in its topic is no match for it.
        self.merge(32, lambda: self.add_text(wanted, "/-- inst_helper holds. -/\ndef inst_helper : Nat := 0"),
                   f"Graph: {a['inst']}\n")
        # A label in bold, which GitHub shows as markup: left out, with a note.
        self.merge(33, lambda: self.add(groups, "bold_thm"))
        self.bodies["33"] = {"body": f"**Graph:** {a['bold']}\n",
                             "html": f'<p dir="auto"><strong>Graph:</strong> {a["bold"]}</p>'}
        # One candidate each, but the page's own dependency sections link a page: not linked.
        self.merge(34, lambda: self.add(wanted, "dep_thm"), f"Graph: {a['dep']}\n")
        self.merge(35, lambda: self.add(wanted, "proofdep_thm"), f"Graph: {a['proofdep']}\n")
        # A word that is no article id, and a label in another case: notes, and the declarations get their pages.
        self.merge(36, lambda: self.add(groups, "odd_thm"), "Graph: af_ABC123, new\n")
        self.merge(37, lambda: self.add(groups, "cased_thm"), f"graph: af_{'e' * 24}\n")
        text = self.description("--base", self.base)
        commit = self.git("rev-parse", "HEAD")
        rows = self.rows()
        self.assertEqual(json.dumps(rows[a["one"]]), json.dumps({
            "subject": before[a["one"]]["subject"], "id": a["one"],
            "object": [{"location": {"declaration": "Ext.count_one"}}], "extensions": {"org.atlas-wiki": {"seed": seed}}}))
        linked = {a["one"]: "Ext.count_one", a["part"]: "Ext.part_thm", a["twice"]: "Ext.twice_b",
                  a["mixed"]: "Ext.mixed_near"}
        for article, name in linked.items():
            self.assertEqual(rows[article]["object"], [{"location": {"declaration": name}}])
        self.assertEqual({article: row for article, row in rows.items() if article in before and article not in linked},
                         {article: row for article, row in before.items() if article not in linked})
        roadmap = self.root / "blueprint/roadmap"
        page = (roadmap / sylow / "sylow-counting.md").read_text()
        self.assertEqual(page, "# Sylow counting\n\nSylow counting holds.\n\n## Sources\n\n- A book.\n")
        pages = {path.name for path in roadmap.rglob("*.md")}
        withheld = ["far_thm", "held_fix", "several_a", "several_b", "shared_thm", "two_a", "two_b", "kindless_thm",
                    "unlisted_thm", "extra_thm", "field_thm", "node_thm", "gap_thm", "ren_a", "wgap_stmt", "van_b",
                    "shouty_thm", "fenced_thm", "inst_helper", "dep_thm", "proofdep_thm"]
        for name in ["count_one", "part_thm", "twice_b", "mixed_near", *withheld]:
            self.assertNotIn(name.replace("_", "-") + ".md", pages)
        for name in ("rings-thm.md", "edited-thm.md", "hidden-thm.md", "mismatch-thm.md", "twice-a.md", "mixed-far.md",
                     "listed-thm.md", "nobody-thm.md", "bold-thm.md", "odd-thm.md", "cased-thm.md"):
            self.assertIn(name, pages)
        state = json.loads((self.root / "scripts/wiki-sync.json").read_text())["docstrings"]
        for name in ["count_one", "part_thm", "twice_b", "mixed_near", *withheld]:
            self.assertEqual(state[f"Ext.{name}"], sync.digest(f"{name} holds."))
        self.assertNotIn("van-a.md", pages)
        self.assertIn("- 4 planned pages that merged pull requests' `Graph:` lines name linked to a declaration; 20 "
                      "left for an editor, and 21 declarations that may state them given no page.", text)
        self.assertEqual((roadmap / sylow / "fenced.md").read_text(), "# Fenced\n\nFenced holds.\n\n```\n## Depends on\n"
                         "```\n\nMore prose.\n\n## Sources\n\n- A book.\n")
        for line in (f"- linked `{a['one']}` (kind `theorem`) to `Ext.count_one` (a Lean `theorem`), from #1's `Graph:` "
                     f"line: `{sylow}/sylow-counting.md`\n",
                     f"- linked `{a['part']}` (kind `theorem`) to `Ext.part_thm` (a Lean `theorem`), from #16's `Graph:` "
                     f"line: `{sylow}/part-01/in-part.md`\n",
                     f"- linked `{a['twice']}` (kind `theorem`) to `Ext.twice_b` (a Lean `theorem`), from #18's `Graph:` "
                     f"line: `{sylow}/twice.md`\n",
                     f"- linked `{a['mixed']}` (kind `theorem`) to `Ext.mixed_near` (a Lean `theorem`), from #20's "
                     f"`Graph:` line: `{sylow}/mixed.md`\n",
                     f"`{a['node']}` (`{basics}/node.md`): #19 names it; it is a node still to expand: expanding or "
                     "linking it is an editor's call; given no page: `Ext.node_thm`",
                     f"`{a['several']}` (`{sylow}/sylow-several.md`): #2 adds 2 documented declarations in its topic "
                     "that could state it; given no page: `Ext.several_a`, `Ext.several_b`",
                     f"`{a['two']}` (`{basics}/two-prs.md`): #3, #4 name it, and the batch does not choose between them; "
                     "given no page: `Ext.two_a`, `Ext.two_b`",
                     f"`{a['far']}` (`{sylow}/far.md`): #9 adds no documented declaration in its topic that could state it, "
                     "only elsewhere; given no page: `Ext.far_thm`",
                     f"`{a['s1']}` (`{sylow}/shared-one.md`): #10 names it; `Ext.shared_thm`, its one candidate, may "
                     "also state another page that a `Graph:` line names; given no page: `Ext.shared_thm`",
                     f"`{a['s2']}` (`{sylow}/shared-two.md`): #10 names it; `Ext.shared_thm`, its one candidate, may "
                     "also state another page that a `Graph:` line names; given no page: `Ext.shared_thm`",
                     f"`{a['held']}` (`{basics}/held.md`): #11 names it; it holds `Ext.held_decl` back: relinking it is an "
                     "editor's call; given no page: `Ext.held_fix`",
                     f"`{a['kindless']}` (`{sylow}/kindless.md`): #12 names it; it records no kind, so the batch cannot "
                     "tell what sort of declaration states it; given no page: `Ext.kindless_thm`",
                     f"`{a['unlisted']}` (`{sylow}/unlisted.md`): #13 names it; its folder page does not list it: listing "
                     "and linking it are an editor's call; given no page: `Ext.unlisted_thm`",
                     f"`{a['extra']}` (`{sylow}/extra.md`): #14 names it; its row holds more than its kind, its "
                     "counterparts and its seed: linking it is an editor's call; given no page: `Ext.extra_thm`",
                     f"`{a['field']}` (`Algebra/groups/in-field.md`): #15 adds documented declarations that could state "
                     "it, but the page sits right in a field's folder, in no topic; given no page: `Ext.field_thm`",
                     f"`{a['gapped']}` (`{sylow}/gapped.md`): #22 names it; its own dependency sections link 1 page(s), "
                     "such as `sylow-several.md`, and the batch cannot tell whether the declaration's Lean records them: "
                     "linking it is an editor's call; given no page: `Ext.gap_thm`",
                     f"`{a['dep']}` (`{sylow}/dep.md`): #34 names it; its own dependency sections link 1 page(s), such as "
                     "`../sylow-theorems/sylow.md`, and the batch cannot tell whether the declaration's Lean records them: "
                     "linking it is an editor's call; given no page: `Ext.dep_thm`",
                     f"`{a['proofdep']}` (`{sylow}/proof-dep.md`): #35 names it; its own dependency sections link 1 "
                     "page(s), such as `sylow.md`, and the batch cannot tell whether the declaration's Lean records them: "
                     "linking it is an editor's call; given no page: `Ext.proofdep_thm`",
                     "#36: 1 word(s) of its `Graph:` line left out, such as `af_ABC123`: an article id is `af_` and 24 "
                     "lower-case hexadecimal digits",
                     "#37: 1 line(s) labelled as a `Graph:` line in another case left out: only `Graph:` counts",
                     f"`{a['renamed']}` (`{sylow}/renamed.md`): #23 adds 2 documented declarations in its topic that "
                     "could state it; given no page: `Ext.ren_a`",
                     f"`{a['wgap']}` (`{sylow}/wanted-gap.md`): #25 names it; its own dependency sections link 1 "
                     "page(s), such as `pre-wanted.md`, and the batch cannot tell whether the declaration's Lean records "
                     "them: linking it is an editor's call; given no page: `Ext.wgap_stmt`",
                     f"`{a['shouty']}` (`{sylow}/shouty.md`): #30 names it; its own dependency sections link 1 page(s), "
                     "such as `../sylow-theorems/sylow.md`, and the batch cannot tell whether the declaration's Lean "
                     "records them: linking it is an editor's call; given no page: `Ext.shouty_thm`",
                     f"`{a['fenced']}` (`{sylow}/fenced.md`): #31 names it; the batch cannot drop its own dependency "
                     "sections exactly as Autoform reads them: linking it is an editor's call; given no page: "
                     "`Ext.fenced_thm`",
                     f"`{a['inst']}` (`{sylow}/inst.md`): #32 names it; it records the kind `instance`, and an instance "
                     "gets no page, so no candidate can state it: linking it is an editor's call; given no page: "
                     "`Ext.inst_helper`",
                     "#33: 1 article id(s) of a `Graph:` line left out: GitHub does not show them on a line of plain "
                     "text",
                     f"`{a['vanish']}` (`{sylow}/vanish.md`): `Ext.van_a`, the one declaration in its topic that #26 "
                     "adds and that could state it, is gone or deprecated on `main` now, and the pull requests that took "
                     "it away add these in its module; given no page: `Ext.van_b`",
                     f"{a['kept']} (#29): it records no kind, so the batch cannot tell what sort of declaration states "
                     "it; #29 adds no candidate the batch would give a page\n",
                     "#28: its `Place:` and `Graph:` lines are left out: its description is not known",
                     f"{a['def']} (#8): #8 adds no documented declaration that could state it\n",
                     f"Pages linked already, 1, by the pull request that names them:\n\n```text\n#5: af_{5:024x}\n```",
                     f"af_{3:024x} (#5): it is a folder page\n",
                     f"af_{'f' * 24} (#5): no row has this article id\n",
                     "#6: its `Graph:` line is left out: its description was edited after the merge",
                     "#7: 1 article id(s) of a `Graph:` line left out: GitHub does not show them on a line of plain text",
                     "#17: its `Graph:` line is left out: its description was edited after the merge",
                     "#21: 1 article id(s) of a `Graph:` line left out: GitHub does not show them on a line of plain "
                     "text"):
            with self.subTest(line=line):
                self.assertIn(line, text)
        for article in (a["edited"], a["hidden"], a["listed"], a["bold"]):
            self.assertNotIn(f"`{article}`", text)
        # verify agrees from main, and prints what make wrote.
        written = self.root.parent / f"{self.root.name}-verify-body.md"
        self.addCleanup(written.unlink, True)
        result = self.tool("verify", commit, "--body", str(written))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("once the 4 planned pages of the link plan are linked, withholding 21 declarations",
                      result.stdout)
        self.assertIn("The declarations it withholds, so with no page: Ext.dep_thm, Ext.extra_thm, Ext.far_thm, ",
                      result.stdout)
        self.assertEqual(written.read_text(), text)

    def test_verify_from_a_newer_main_keeps_the_link(self) -> None:
        article = "af_" + "a" * 24
        self.planned("Algebra/groups/sylow-theorems/sylow-counting.md", article)
        self.base = self.commit("a planned page")
        self.merge(1, lambda: self.add("WantedExt/Algebra/SylowWanted.lean", "count_one"), f"Graph: {article}\n")
        through = self.git("rev-parse", "HEAD")
        made = self.description("--base", self.base)
        commit = self.git("rev-parse", "HEAD")
        # main merges more Lean after the batch was made: the batch still merges, with its link.
        self.git("reset", "-q", "--hard", through)
        self.merge(2, lambda: self.module("MathlibExt/Algebra/Other.lean", ["other"]))
        written = self.root.parent / f"{self.root.name}-verify-body.md"
        self.addCleanup(written.unlink, True)
        result = self.tool("verify", commit, "--body", str(written))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("once the 1 planned pages of the link plan are linked", result.stdout)
        self.assertIn("merges cleanly into", result.stdout)
        self.assertEqual(written.read_text(), made)

    def test_verify_refuses_a_link_that_is_not_the_plans(self) -> None:
        article = "af_" + "a" * 24
        self.planned("Algebra/groups/sylow-theorems/sylow-counting.md", article)
        # A `## Depends on` that links nothing, which a linked page loses.
        page = self.root / "blueprint/roadmap/Algebra/groups/sylow-theorems/sylow-counting.md"
        page.write_text(page.read_text().replace("\n## Sources", "\n## Depends on\n\nNothing named yet.\n\n## Sources"))
        self.base = self.commit("a planned page")
        self.merge(1, lambda: self.add("WantedExt/Algebra/SylowWanted.lean", "count_one"), f"Graph: {article}\n")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        self.assertEqual(self.rows()[article]["object"], [{"location": {"declaration": "Ext.count_one"}}])
        message = self.git("log", "-1", "--format=%B")
        # The page keeps its own dependency sections: not what the batch writes.
        self.git("checkout", "HEAD^", "--", "blueprint/roadmap/Algebra/groups/sylow-theorems/sylow-counting.md")
        self.git("commit", "-q", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("does not find the batch's wiki exactly the sync's", result.stderr)
        # Nor is a batch that leaves the page planned and gives its declaration a page of its own.
        self.git("reset", "-q", "--hard", "HEAD^")
        self.bodies["1"] = "Graph: new\n"
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        self.assertTrue((self.root / "blueprint/roadmap/Algebra/groups/sylow-theorems/count-one.md").is_file())
        self.bodies["1"] = f"Graph: {article}\n"
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("does not find the batch's wiki exactly the sync's", result.stderr)

    def test_an_editors_link_lets_the_next_batch_give_the_others_their_pages(self) -> None:
        article = "af_" + "b" * 24
        page = "Algebra/groups/sylow-theorems/sylow-several.md"
        self.planned(page, article)
        self.base = self.commit("a planned page")
        self.merge(1, lambda: self.module("MathlibExt/Algebra/Several.lean", ["several_a", "several_b"]),
                   f"Graph: {article} new\nPlace: MathlibExt/Algebra/Several -> Algebra/groups | Sylow theorems\n")
        self.assertIn("given no page: `Ext.several_a`, `Ext.several_b`", self.description("--base", self.base))
        self.land(2, "batch-1")

        # An editor links the page to the declaration that states it, in a graph pull request.
        def link() -> None:
            links = self.root / "blueprint/links/Algebra.jsonl"
            links.write_text(links.read_text().replace(
                f'"id": "{article}", "extensions": {{"org.atlas-wiki": {{"kind": "theorem"}}}}',
                f'"id": "{article}", "object": [{{"location": {{"declaration": "Ext.several_a"}}}}]'))

        self.merge(3, link, f"Graph: {article}\n")
        self.assertEqual(self.rows()[article]["object"], [{"location": {"declaration": "Ext.several_a"}}])
        # A batch from the same base gives the other its page, beside the linked one.
        text = self.description("--base", self.base)
        roadmap = self.root / "blueprint/roadmap/Algebra/groups/sylow-theorems"
        self.assertTrue((roadmap / "several-b.md").is_file())
        self.assertFalse((roadmap / "several-a.md").exists())
        self.assertIn(f"```text\n#1: {article}\n#3: {article}\n```", text)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
