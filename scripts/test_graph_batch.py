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


if __name__ == "__main__":
    unittest.main()
