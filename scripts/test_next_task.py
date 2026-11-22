#!/usr/bin/env python3
"""next_task.py picks ready tasks that no pull request names, offline: GitHub and the site are stubbed."""

from __future__ import annotations

import gzip
import io
import json
import os
import sys
import tempfile
import unittest
import urllib.error
import urllib.request
from contextlib import redirect_stderr, redirect_stdout
from email.message import Message
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import next_task  # noqa: E402

REPO = "facebookresearch/atlas-lean"
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
         updated_at: str = "2026-11-21T00:00:00Z", base: str = "main") -> dict:
    return {"number": number, "title": title, "body": body, "head": {"ref": branch}, "base": {"ref": base},
            "merged_at": merged_at, "updated_at": updated_at}


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

    def __call__(self, url: str, token: str | None = None) -> bytes:
        self.read.append((url, token))
        return self.pages.get(url, b"[]")


def run(site: Site, *args: str, env: dict | None = None) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with mock.patch.object(next_task, "request", site), mock.patch.dict(os.environ, env or {}, clear=True), \
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
        # One page of each kind, as each holds fewer than a full page; no token was set.
        self.assertEqual(site.read, [(next_task.TASKS, None), (OPEN + "1", None), (CLOSED + "1", None)])

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
                 body="Proves the `fejer` statement in `WantedExt/Analysis/FourierConvergenceWanted.lean`."),
            # A distinctive short name in a title.
            pull(32, title="WantedExt: require a finite set in breuillard_green_tao_approximate_subgroup"),
            # A common word, an ambiguous name, a short name without its module, and one in prose.
            pull(33, body="A Möbius map `S z = (a z + b) / (c z + d)` with `add` and `succ` from `A`."),
            pull(34, body="The naive bound `naiveUpperThree` of `SquareBoundsWanted`, as green_tao_density says."),
            # Another declaration that ends with the same name.
            pull(35, body="Uses `Other.breuillard_green_tao_approximate_subgroup`."),
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
        longer = pull(85, body="`Geometry.JacobianChallengeWanted.JacobianChallenge.genus`")
        self.assertEqual(next_task.taken(items, [longer]), {"Algebra/t71": [85]})
        # Two declarations end with `JacobianChallenge.genus` and three with `genus`, and a name in prose is no code.
        self.assertEqual(next_task.taken(items, [pull(82, title="Define JacobianChallenge.genus"),
                                                 pull(83, body="`genus`"), pull(84, body="As in Faltings.genus.")]), {})

    def test_code_is_read_as_markdown_reads_it(self) -> None:
        name = "breuillard_green_tao_approximate_subgroup"
        items = [item(91, "proof", f"MetaMathlibExt.{name}"), item(92, "proof", "MetaMathlibExt.green_tao_density")]
        # The prose between a fenced block and a code span is no code, and the span after the block is.
        prose = f"```lean\n#check Nat\n```\n\nUnlike {name}, this changes `foo`."
        self.assertEqual(next_task.taken(items, [pull(101, body=prose)]), {})
        claim = f"```lean\n#check Nat\n```\n\nProves `{name}`."
        self.assertEqual(next_task.taken(items, [pull(104, body=claim)]), {"Algebra/t91": [104]})
        # Fenced blocks of backticks or tildes, one left open, and a span of two backticks are code.
        for body in (f"```lean\n#check {name}\n```", f"~~~\n{name}\n~~~", f"````\n{name}", f"Proves ``{name}``."):
            self.assertEqual(next_task.taken(items, [pull(102, body=body)]), {"Algebra/t91": [102]}, body)
        # A backtick fence's info string holds no backtick, so this line is a code span, not a fence.
        self.assertEqual(next_task.taken(items, [pull(103, body="``` `green_tao_density` ```\nUnlike " + name)]),
                         {"Algebra/t92": [103]})
        # A code span over two lines of a paragraph, and fenced blocks in a quote and in a list, are code too.
        for body in (f"Proves `theorem\n{name} : True`.", f"> ```lean\n> #check {name}\n> ```",
                     f"- ```lean\n  #check {name}\n  ```"):
            self.assertEqual(next_task.taken(items, [pull(105, body=body)]), {"Algebra/t91": [105]}, body)
        # A fence indented by four spaces opens no block, and a block in a quote ends with the quote, so the prose after
        # either is no code.
        for body in (f"    ```lean\n{name}\n    ```", f"> ```lean\n> #check Nat\nUnlike {name}, this changes `foo`.",
                     f"> ```lean\n> #check Nat\n\nUnlike {name}, this changes `foo`."):
            self.assertEqual(next_task.taken(items, [pull(107, body=body)]), {}, body)
        # Escaped backticks are prose, and a blank line ends a paragraph and any span in it.
        for body in (f"Unlike \\`{name}\\`, this changes `foo`.", f"A ` here.\n\nUnlike {name}, this changes `foo`."):
            self.assertEqual(next_task.taken(items, [pull(106, body=body)]), {}, body)

    def test_a_block_ends_with_the_list_item_or_quote_that_holds_it(self) -> None:
        name = "breuillard_green_tao_approximate_subgroup"
        items = [item(91, "proof", f"MetaMathlibExt.{name}"), item(92, "proof", "MetaMathlibExt.green_tao_density")]
        # A list item's lines are indented to where its content starts, so is the fence that closes a block in it, and
        # the block is code, a block opened on a later line of the item and a paragraph's lazy line included.
        for body in (f"-   ```lean\n    #check {name}\n    ```",
                     f"- Proves\nthe bound:\n  ```lean\n  #check {name}\n  ```"):
            self.assertEqual(next_task.taken(items, [pull(111, body=body)]), {"Algebra/t91": [111]}, body)
        # The prose after such a block is no code, nor is the line that ends the list item, and the block with it. A
        # quote opening ends a paragraph, so a span does not run into it, and a list item that began with a blank
        # line ends at a second one.
        for body in (f"-   ```lean\n    #check Nat\n    ```\n\nUnlike {name}, this changes `foo`.",
                     f"1.  ```lean\n    #check Nat\n    ```\n\nUnlike {name}, this changes `foo`.",
                     f"-   ```lean\n    #check Nat\nUnlike {name}, this changes `foo`.",
                     f"- Tests:\n\n  ```\n  #check Nat\nUnlike {name}, this changes `foo`.",
                     f"A ` here\n> Unlike {name}, this changes `foo`.", f"-\n\n    ```\n    {name}\n    ```"):
            self.assertEqual(next_task.taken(items, [pull(112, body=body)]), {}, body)

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
        self.assertEqual(next_task.taken(items, [pull(54, body="Proves `Ext.sum?`.")]), {"Algebra/t46": [54]})
        self.assertEqual(next_task.taken(items, [pull(55, body="Is it Ext.sum?")]),
                         {"Algebra/t45": [55], "Algebra/t46": [55]})
        # Emphasis around a name, Lean's `_root_.` prefix, and universes after it.
        for body in (f"Proves _{fejer}_.", f"Proves `_root_.{fejer}`.", f"Proves `{fejer}.{{u}}`."):
            self.assertEqual(next_task.taken(items, [pull(56, body=body)]), {"Algebra/t47": [56]}, body)

    def test_a_pull_request_merged_into_another_branch_takes_nothing(self) -> None:
        merged = [pull(61, body="Ext.p1", merged_at="2026-11-20T13:00:00Z", updated_at="2026-11-20T13:00:00Z",
                       base="feature")]
        _, out, _ = run(Site(open_pages=([],), closed_pages=(merged,)), "--json")
        self.assertEqual(json.loads(out)["taken_by"], [])

    def test_the_count_is_positive(self) -> None:
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            next_task.main(["-n", "0"])


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
            self.assertEqual(request.get_header("Accept"), "application/vnd.github+json")
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
