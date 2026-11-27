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
import urllib.parse
import urllib.request
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timedelta, timezone
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
# GitHub's search of the pull requests merged into main.
SEARCH = f"{next_task.API}/search/issues?"
TOKEN = {"GH_TOKEN": "secret"}


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
# Pull requests merged into main, which GitHub's search finds by their merge times, and GraphQL lists by their last
# update: #4 merged after the list's commit, and #5 before it.
MERGED_PULLS = {
    4: pull(4, body=f"Done: `{ITEMS[5]['lean_targets'][0]['declaration']}`", merged_at="2026-11-20T18:00:00Z"),
    5: pull(5, body="Ext.p5", merged_at="2026-11-20T11:00:00Z"),
}


def stamp(text: str) -> datetime:
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


class Site:
    """The site and GitHub's API, as next_task.request reads them: the open pull requests, the search of those merged
    into main (all of *merged* but the *unindexed* ones, which the search does not show yet), and GraphQL. GraphQL
    gives each pull request of *merged* and nothing for any other number, and lists those of *merged* merged into
    main by their last update, newest first, a page after a cursor at a time; *moves* maps the number of a listing
    request to a change of *merged* made right after it is answered, as when a pull request is updated meanwhile."""

    def __init__(self, tasks: dict | None = None, open_pages=(OPEN_PULLS,), merged: dict | None = None, unindexed=(),
                 moves: dict | None = None) -> None:
        self.pages = {next_task.TASKS: json.dumps(tasks or TASKS).encode()}
        for number, rows in enumerate(open_pages, 1):
            self.pages[f"{OPEN}{number}"] = json.dumps(rows).encode()
        self.merged = dict(MERGED_PULLS if merged is None else merged)
        self.unindexed = set(unindexed)
        self.moves = moves or {}
        self.read: list[tuple[str, str | None]] = []
        self.media: list[str] = []
        self.searched: list[tuple[str, int, int]] = []
        self.asked: list[list[int]] = []
        self.listings: list[str | None] = []

    def __call__(self, url: str, token: str | None = None, media: str | None = None,
                 data: bytes | None = None) -> bytes:
        self.read.append((url, token))
        if url == next_task.GRAPHQL:
            sent = json.loads(data)
            return self.listing(sent) if "pullRequests(states: [MERGED]" in sent["query"] else self.graphql_answer(sent)
        if url.startswith(next_task.API):
            self.media.append(media)
        if url.startswith(SEARCH):
            return json.dumps(self.search(url)).encode()
        return self.pages.get(url, b"[]")

    def search(self, url: str) -> dict:
        fields = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)
        query, page = fields["q"][0], int(fields["page"][0])
        assert (fields["sort"], fields["order"], fields["per_page"]) == (["created"], ["asc"], ["100"]), fields
        terms = query.split()
        assert terms[:4] == [f"repo:{REPO}", "is:pr", "is:merged", "base:main"], query
        start, end = (stamp(part) for part in terms[4].removeprefix("merged:").split(".."))
        found = sorted(number for number, row in self.merged.items()
                       if row["base"]["ref"] == "main" and number not in self.unindexed
                       and start <= stamp(row["merged_at"]) <= end)
        self.searched.append((terms[4], len(found), page))
        return {"total_count": len(found), "incomplete_results": False,
                "items": [{"number": number} for number in found[(page - 1) * 100:page * 100]]}

    def listing(self, sent: dict) -> bytes:
        variables, query = sent["variables"], sent["query"]
        assert (variables["owner"], variables["name"]) == ("facebookresearch", "atlas-lean")
        assert 'baseRefName: "main"' in query and "orderBy: {field: UPDATED_AT, direction: DESC}" in query, query
        rows = sorted((row for row in self.merged.values() if row["base"]["ref"] == "main"),
                      key=lambda row: (row["updated_at"], row["number"]), reverse=True)
        if variables["after"] is not None:
            last = tuple(json.loads(variables["after"]))
            rows = [row for row in rows if (row["updated_at"], row["number"]) < last]
        page = rows[:100]
        self.listings.append(variables["after"])
        answer = {"data": {"repository": {"pullRequests": {
            "pageInfo": {"endCursor": json.dumps([page[-1]["updated_at"], page[-1]["number"]]) if page else None,
                         "hasNextPage": len(rows) > 100},
            "nodes": [{"number": row["number"], "updatedAt": row["updated_at"], "mergedAt": row["merged_at"]}
                      for row in page]}}}}
        if move := self.moves.get(len(self.listings)):
            move(self.merged)
        return json.dumps(answer).encode()

    def graphql_answer(self, sent: dict) -> bytes:
        # The pull requests the query names, under their aliases; a number that is no pull request gives null.
        assert sent["variables"] == {"owner": "facebookresearch", "name": "atlas-lean"}
        numbers = [int(number) for number in re.findall(r"p(\d+): pullRequest\(number: \1\)", sent["query"])]
        self.asked.append(numbers)
        found = {f"p{number}": self.graphql(self.merged[number]) if number in self.merged else None
                 for number in numbers}
        return json.dumps({"data": {"repository": found}}).encode()

    @staticmethod
    def graphql(row: dict) -> dict:
        return {"number": row["number"], "title": row["title"], "body": row["body"], "bodyHTML": row["body_html"],
                "headRefName": row["head"]["ref"], "baseRefName": row["base"]["ref"], "mergedAt": row["merged_at"]}


def updated(row: dict, when: str) -> dict:
    return {**row, "updated_at": when}


def before(seconds: int, at: str = "2026-11-21T09:00:00Z") -> str:
    """The time *seconds* before *at*, as GitHub writes it."""
    return (stamp(at) - timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


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
        code, out, err = run(site, "--json", "-n", "10", env=TOKEN)
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
        # One page of open pull requests, one of those merged into main by their last update, and one of the search,
        # as each holds fewer than a full page, then the merged pull request found: open and merged pull requests come
        # with their bodies as GitHub renders them.
        read = [(SEARCH if url.startswith(SEARCH) else url, token) for url, token in site.read]
        self.assertEqual(read, [(next_task.TASKS, None), (OPEN + "1", "secret"), (next_task.GRAPHQL, "secret"),
                                (SEARCH, "secret"), (next_task.GRAPHQL, "secret")])
        self.assertEqual(site.media, [next_task.RENDERED, None])
        self.assertEqual(site.listings, [None])
        self.assertEqual(site.asked, [[4]])

    def test_the_text_lists_the_next_n_with_what_takes_them(self) -> None:
        code, out, _ = run(Site(), "-n", "2", env=TOKEN)
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
        code, out, _ = run(Site(tasks=tasks, open_pages=([],), merged={}), "-n", "1", env=TOKEN)
        self.assertEqual(code, 0)
        for character in ("\x1b", "\x07", "\x9b", "\nforged"):
            self.assertNotIn(character, out)
        self.assertIn("T\\x1b]0;owned\\x07\\nforged: line\\x9b2J", out)
        code, out, _ = run(Site(tasks=tasks, open_pages=([],), merged={}), "--json", env=TOKEN)
        self.assertTrue(out.isascii())
        self.assertEqual(json.loads(out)["next"], [task])

    def test_every_page_of_open_pull_requests_is_read(self) -> None:
        filler = [pull(100 + number) for number in range(100)]
        site = Site(open_pages=(filler, [pull(7, body=ITEMS[0]["article_id"].upper())]))
        _, out, _ = run(site, "--json", env=TOKEN)
        self.assertIn({"node_id": "Algebra/t1", "pull_requests": [7]}, json.loads(out)["taken_by"])
        self.assertEqual([url for url, _ in site.read if url.startswith(OPEN)], [OPEN + "1", OPEN + "2"])

    def test_merged_pull_requests_are_searched_by_merge_time_up_to_now(self) -> None:
        # However they were merged, by the queue, a squash, a rebase or as part of another pull request, and however
        # many other pull requests were closed or touched since the list's commit, the search finds those merged.
        before = datetime.now(timezone.utc).replace(microsecond=0)
        site = Site(open_pages=([],))
        _, out, _ = run(site, "--json", env=TOKEN)
        self.assertEqual(json.loads(out)["taken_by"], [{"node_id": "Algebra/t6", "pull_requests": [4]}])
        (merged, count, page), = site.searched
        start, end = (stamp(part) for part in merged.removeprefix("merged:").split(".."))
        self.assertEqual(start, stamp("2026-11-20T12:00:00Z"))
        self.assertTrue(before <= end <= datetime.now(timezone.utc), end)
        self.assertEqual((count, page), (1, 1))

    def test_a_span_with_more_than_the_search_lists_is_searched_in_halves(self) -> None:
        # 450 merges over six hours, of which the search lists at most 200 at a time.
        merged = {1000 + n: pull(1000 + n, merged_at=f"2026-11-20T{12 + n // 75:02d}:{n % 75 * 47 // 60:02d}:"
                                                     f"{n % 60:02d}Z") for n in range(450)}
        merged[10] = pull(10, body="Ext.p1", merged_at="2026-11-20T13:00:00Z")
        site = Site(open_pages=([],), merged=merged)
        with mock.patch.object(next_task, "SEARCH_PAGES", 2):
            _, out, _ = run(site, "--json", env=TOKEN)
        self.assertEqual(json.loads(out)["taken_by"], [{"node_id": "Algebra/t1", "pull_requests": [10]}])
        # Every merge is read once, in batches of 100, and no search span read past its first page counted more
        # than the search lists.
        self.assertEqual(sorted(number for numbers in site.asked for number in numbers), sorted(merged))
        self.assertEqual([len(numbers) for numbers in site.asked], [100, 100, 100, 100, 51])
        self.assertTrue(all(count <= 200 for _, count, page in site.searched if page > 1))
        self.assertGreater(len({merged for merged, _, _ in site.searched}), 2)

    def test_a_pull_request_merged_in_the_commits_second_counts(self) -> None:
        # GitHub's times are to the second, as the commit's: one merged in its second may be missing from the list.
        merged = {13: pull(13, body="Ext.p1", merged_at="2026-11-20T12:00:00Z"),
                  14: pull(14, body="Ext.s1", merged_at="2026-11-20T11:59:59Z")}
        _, out, _ = run(Site(open_pages=([],), merged=merged), "--json", env=TOKEN)
        taken = {row["node_id"]: row["pull_requests"] for row in json.loads(out)["taken_by"]}
        self.assertEqual(taken, {"Algebra/t1": [13]})

    def test_one_the_search_does_not_show_yet_is_read_from_those_merged_and_updated_in_the_last_lag(self) -> None:
        # Merged pull requests by their last update: 100 merged before the list's commit and updated later, then one
        # merged since that the search does not show yet, on the second page. The script reads pages until one ends
        # before the last LAG (here long enough to reach back to the list's commit), then the first page again.
        merged = {300 + n: pull(300 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(n)) for n in range(100)}
        merged[15] = pull(15, body="Ext.p1", merged_at="2026-11-20T19:00:00Z", updated_at="2026-11-20T19:00:00Z")
        merged[16] = pull(16, merged_at="2026-11-19T00:00:00Z", updated_at="2026-11-20T11:00:00Z")
        site = Site(open_pages=([],), merged=merged, unindexed={15})
        with mock.patch.object(next_task, "LAG", timedelta(days=36500)):
            _, out, _ = run(site, "--json", env=TOKEN)
        self.assertEqual(json.loads(out)["taken_by"], [{"node_id": "Algebra/t1", "pull_requests": [15]}])
        self.assertEqual([after is None for after in site.listings], [True, False, True])
        self.assertEqual(site.asked, [[15]])
        # With the last LAG ten minutes, those updated on 21 November are older, so the first page is enough, and
        # the search is trusted to show those merged before then.
        site = Site(open_pages=([],), merged=merged, unindexed={15})
        _, out, _ = run(site, "--json", env=TOKEN)
        self.assertEqual(site.listings, [None])

    def test_one_updated_while_the_pages_are_read_makes_none_skip_and_is_read_too(self) -> None:
        older = {300 + n: pull(300 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(n)) for n in range(100)}
        middle = {400 + n: pull(400 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(3600 + n))
                  for n in range(100)}
        late = pull(15, body="Ext.p1", merged_at="2026-11-21T07:00:00Z", updated_at="2026-11-21T07:00:00Z")
        old = pull(16, merged_at="2026-11-19T00:00:00Z", updated_at="2026-11-20T11:00:00Z")
        base = {**older, **middle, 15: late, 16: old}
        # One on page 2 is updated right after GitHub answers it: it moves ahead of the cursor, and as a merged pull
        # request never leaves the list, #15 does not move past the start of page 3.
        moves = {2: lambda merged: merged.update({499: updated(merged[499], "2026-11-21T10:00:00Z")})}
        # #15 itself is updated right after GitHub answers page 1: it moves ahead of the cursor, and the first page,
        # read again at the end, holds it.
        moved = {1: lambda merged: merged.update({15: updated(merged[15], "2026-11-21T10:00:00Z")})}
        for scene in (moves, moved):
            site = Site(open_pages=([],), merged=base, unindexed={15}, moves=scene)
            with mock.patch.object(next_task, "LAG", timedelta(days=36500)):
                code, out, err = run(site, "--json", env=TOKEN)
            self.assertEqual((code, err), (0, ""), scene)
            self.assertEqual(json.loads(out)["taken_by"], [{"node_id": "Algebra/t1", "pull_requests": [15]}])
        # A first page that, read again, does not reach past the newest update of the first read may hide one, and
        # more pages in the last LAG than it reads stop it.
        flood = {600 + n: pull(600 + n, merged_at="2026-11-19T00:00:00Z", updated_at="2026-11-19T12:00:00Z")
                 for n in range(100)}
        flooded = {2: lambda merged: merged.update({number: updated(merged[number], "2026-11-21T10:00:00Z")
                                                    for number in flood})}
        recent = {700 + n: pull(700 + n, merged_at="2026-11-19T00:00:00Z", updated_at="2026-11-21T09:00:00Z")
                  for n in range(300)}
        cases = ((Site(merged={**older, 16: old, **flood}, moves=flooded), "updated while this script read them"),
                 (Site(merged=recent), "more than 200 pull requests merged into main were updated since"))
        for site, message in cases:
            with mock.patch.object(next_task, "LAG", timedelta(days=36500)), \
                    mock.patch.object(next_task, "TAIL_PAGES", 2):
                code, _, err = run(site, "--json", env=TOKEN)
            self.assertEqual(code, 1, message)
            self.assertIn(message, err)

    def test_one_updated_in_the_second_of_the_newest_update_is_not_missed(self) -> None:
        # The first page's newest two were updated at 09:00:00. Right after it is read, #15, merged two hours ago on a
        # later page, is updated in that same second: it sorts behind those two, ahead of the cursor.
        tied = {900 + n: pull(900 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(0)) for n in range(2)}
        rest = {300 + n: pull(300 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(60 + n)) for n in range(98)}
        middle = {400 + n: pull(400 + n, merged_at="2026-11-19T00:00:00Z", updated_at=before(3600 + n))
                  for n in range(98)}
        late = pull(15, body="Ext.p1", merged_at="2026-11-21T07:00:00Z", updated_at="2026-11-21T07:00:00Z")
        old = pull(16, merged_at="2026-11-19T00:00:00Z", updated_at="2026-11-20T11:00:00Z")
        base = {**tied, **rest, **middle, 15: late, 16: old}

        def owner(merged: dict) -> None:
            merged[15] = updated(merged[15], before(0))

        def owner_then_others(merged: dict) -> None:
            owner(merged)
            merged.update({number: updated(merged[number], "2026-11-21T09:30:00Z") for number in middle})

        # The first page, read again, ends past 09:00:00 and holds #15.
        site = Site(open_pages=([],), merged=base, unindexed={15}, moves={1: owner})
        with mock.patch.object(next_task, "LAG", timedelta(days=36500)):
            code, out, err = run(site, "--json", env=TOKEN)
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(json.loads(out)["taken_by"], [{"node_id": "Algebra/t1", "pull_requests": [15]}])
        # With 98 more updated later, the page read again ends with the two at 09:00:00, and #15 comes after it: the
        # script cannot tell, and stops.
        site = Site(open_pages=([],), merged=base, unindexed={15}, moves={1: owner_then_others})
        with mock.patch.object(next_task, "LAG", timedelta(days=36500)):
            code, out, err = run(site, "--json", env=TOKEN)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("updated while this script read them", err)

    def test_merged_pull_requests_need_a_token_and_a_search_it_cannot_trust_stops_it(self) -> None:
        # A token is needed whenever the list records its commit date, to read what was merged since.
        for site in (Site(), Site(merged={})):
            code, out, err = run(site, "--json")
            self.assertEqual((code, out), (1, ""))
            self.assertIn("needs a token, as they come from GitHub's GraphQL API: set GH_TOKEN", err)
        for answer, message in (({"total_count": 1, "incomplete_results": True, "items": [{"number": 4}]},
                                 "GitHub's search timed out"),
                                ({"total_count": 2, "incomplete_results": False, "items": [{"number": 4}]},
                                 "listed fewer pull requests merged into main than it counted"),
                                ({"message": "Validation Failed"}, "GitHub's search did not list")):
            site = Site()
            with mock.patch.object(site, "search", lambda url, answer=answer: answer):
                code, _, err = run(site, "--json", env=TOKEN)
            self.assertEqual(code, 1, answer)
            self.assertIn(message, err)
        # The highest count of any page holds: a later page that counts fewer does not hide those missing.
        pages = {1: {"total_count": 150, "incomplete_results": False,
                     "items": [{"number": 600 + n} for n in range(100)]},
                 2: {"total_count": 120, "incomplete_results": False,
                     "items": [{"number": 700 + n} for n in range(20)]}}
        site = Site()
        with mock.patch.object(site, "search", lambda url: pages[int(urllib.parse.parse_qs(url)["page"][0])]):
            code, _, err = run(site, "--json", env=TOKEN)
        self.assertEqual(code, 1)
        self.assertIn("listed fewer pull requests merged into main than it counted", err)
        # Halves that together list fewer than the whole span counted stop it too.
        merged = {**{700 + n: pull(700 + n, merged_at="2026-11-20T13:00:00Z") for n in range(50)},
                  **{800 + n: pull(800 + n, merged_at="2026-11-22T13:00:00Z") for n in range(50)}}
        site = Site(merged=merged)
        real, calls = site.search, []

        def overcounted(url: str) -> dict:
            calls.append(url)
            answer = real(url)
            return {**answer, "total_count": answer["total_count"] + 1} if len(calls) == 1 else answer

        with mock.patch.object(site, "search", overcounted), mock.patch.object(next_task, "SEARCH_PAGES", 1):
            code, _, err = run(site, "--json", env=TOKEN)
        self.assertEqual(code, 1)
        self.assertGreater(len(calls), 1)
        self.assertIn("listed fewer pull requests merged into main than it counted", err)
        # More merges in one second than the search lists.
        crowd = {2000 + n: pull(2000 + n, merged_at="2026-11-20T13:00:00Z") for n in range(101)}
        with mock.patch.object(next_task, "SEARCH_PAGES", 1):
            code, _, err = run(Site(merged=crowd), "--json", env=TOKEN)
        self.assertEqual(code, 1)
        self.assertIn("more than 100 pull requests were merged into main at 2026-11-20T13:00:00Z", err)

    def test_any_graphql_error_or_missing_pull_request_stops_it(self) -> None:
        good = Site.graphql(MERGED_PULLS[4])
        for answer, message in (({"data": {"repository": {"p4": None}},
                                  "errors": [{"type": "INTERNAL", "path": ["repository", "p4"]}]}, "INTERNAL"),
                                ({"data": {"repository": {}}}, "gave no pull request #4"),
                                ({"data": {"repository": {"p4": {**good, "number": 5}}}}, "gave no pull request #4"),
                                ({"data": {"repository": {"p4": good}}, "errors": [{"message": "Something"}]},
                                 "Something"),
                                ({"errors": [{"message": "Bad credentials"}]}, "Bad credentials")):
            site = Site()
            with mock.patch.object(site, "graphql_answer", lambda sent, answer=answer: json.dumps(answer).encode()):
                code, _, err = run(site, "--json", env=TOKEN)
            self.assertEqual(code, 1, answer)
            self.assertIn("GitHub's GraphQL API", err)
            self.assertIn(message, err)
        # So does a listing of those merged into main that holds an error or lacks what it should.
        for answer, message in (({"errors": [{"type": "RATE_LIMITED"}]}, "RATE_LIMITED"),
                                ({"data": {"repository": {"pullRequests": {"nodes": []}}}}, "did not list")):
            site = Site()
            with mock.patch.object(site, "listing", lambda sent, answer=answer: json.dumps(answer).encode()):
                code, _, err = run(site, "--json", env=TOKEN)
            self.assertEqual(code, 1, answer)
            self.assertIn(message, err)

    def test_a_list_without_a_commit_date_is_checked_against_open_pull_requests_only(self) -> None:
        plain = {key: value for key, value in TASKS.items() if key not in ("commit", "commit_date", "autoform_ref")}
        site = Site(tasks=plain)
        code, out, _ = run(site)
        self.assertEqual(code, 0)
        self.assertEqual([url for url, _ in site.read], [next_task.TASKS, OPEN + "1"])
        self.assertIn("records no commit date, so pull requests merged since it was computed are not read", out)

    def test_a_local_file_is_read(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "tasks.json"
            path.write_text(json.dumps(TASKS))
            site = Site()
            code, out, _ = run(site, "--tasks", str(path), "--json", "-n", "1", env=TOKEN)
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
        site = Site(tasks=tasks, open_pages=(pulls,), merged={})
        _, out, _ = run(site, "--json", "-n", "1", env=TOKEN)
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
        merged = {61: pull(61, body="Ext.p1", merged_at="2026-11-20T13:00:00Z", base="feature")}
        _, out, _ = run(Site(open_pages=([],), merged=merged), "--json", env=TOKEN)
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
            code, out, err = run(Site(), "--json", "-n", "10", "--priorities", str(path), env=TOKEN)
            self.assertEqual((code, err), (0, ""))
            result = json.loads(out)
            # The free tasks are t2 (a statement), then the proofs t1, t4 and t7 in tasks.json's order.
            self.assertEqual([task["node_id"] for task in result["next"]], ["Algebra/t2", "Algebra/t7", "Algebra/t4",
                                                                            "Algebra/t1"])
            self.assertEqual(result["next"][1], ITEMS[6])
            self.assertEqual(result["priority"], {"Algebra/t2": 0.5, "Algebra/t7": 2, "Algebra/t4": 1,
                                                  "Algebra/t1": 0.5})
            self.assertEqual(result["priorities"], str(path))
            code, out, _ = run(Site(), "-n", "2", "--priorities", str(path), env=TOKEN)
        self.assertEqual(code, 0)
        self.assertIn(f"Priorities from {path}.", out)
        self.assertIn("proof: Task 7\n  article id   af_000000000000000000000007\n  node         Algebra/t7\n"
                      "  Lean         Ext.p5\n  article      blueprint/roadmap/Algebra/t7.md\n  priority     2", out)
        self.assertNotIn("Task 4", out)

    def test_the_checkouts_file_is_the_default_and_without_it_all_weigh_the_same(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = self.write(folder, PRIORITIES)
            _, out, _ = run(Site(), "--json", "-n", "10", priorities=path, env=TOKEN)
            self.assertEqual([task["node_id"] for task in json.loads(out)["next"]][:2], ["Algebra/t2", "Algebra/t7"])
            self.assertEqual(json.loads(out)["priorities"], str(path))
            missing = Path(folder) / "missing.json"
            _, out, _ = run(Site(), "--json", "-n", "10", priorities=missing, env=TOKEN)
            result = json.loads(out)
            self.assertEqual([task["node_id"] for task in result["next"]], ["Algebra/t2", "Algebra/t1", "Algebra/t4",
                                                                            "Algebra/t7"])
            self.assertEqual((result["priorities"], set(result["priority"].values())), (None, {1}))
            _, out, _ = run(Site(), "-n", "1", priorities=missing, env=TOKEN)
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
    def requests(self, env: dict, code: int = 0) -> list:
        sent = []

        def urlopen(request, timeout):
            sent.append(request)
            if request.full_url == next_task.TASKS:
                body = TASKS
            elif request.full_url.startswith(SEARCH):
                body = {"total_count": 0, "incomplete_results": False, "items": []}
            elif request.full_url == next_task.GRAPHQL:
                body = {"data": {"repository": {"pullRequests": {
                    "pageInfo": {"endCursor": None, "hasNextPage": False}, "nodes": []}}}}
            else:
                body = []
            return mock.MagicMock(**{"__enter__.return_value.read.return_value": json.dumps(body).encode()})

        with mock.patch.object(next_task.OPENER, "open", urlopen), mock.patch.dict(os.environ, env, clear=True), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(next_task.main([]), code)
        return sent

    def test_the_token_goes_to_the_github_api_only(self) -> None:
        sent = self.requests({"GH_TOKEN": "secret"})
        self.assertEqual([request.full_url.partition("?")[0] + "?" for request in sent],
                         [next_task.TASKS + "?", OPEN.partition("?")[0] + "?", next_task.GRAPHQL + "?", SEARCH])
        self.assertIsNone(sent[0].get_header("Authorization"))
        for request in sent[1:]:
            self.assertEqual(request.get_header("Authorization"), "Bearer secret")
        self.assertEqual([request.get_header("Accept") for request in sent[1:]],
                         [next_task.RENDERED, "application/vnd.github+json", "application/vnd.github+json"])
        self.assertEqual(self.requests({"GITHUB_TOKEN": "other"})[1].get_header("Authorization"), "Bearer other")

    def test_merged_pull_requests_are_asked_of_graphql_with_the_token(self) -> None:
        sent = []

        def urlopen(request, timeout):
            sent.append(request)
            if request.full_url == next_task.TASKS:
                body = TASKS
            elif request.full_url == next_task.GRAPHQL and b"pullRequests(states" in request.data:
                body = {"data": {"repository": {"pullRequests": {
                    "pageInfo": {"endCursor": None, "hasNextPage": False}, "nodes": []}}}}
            elif request.full_url == next_task.GRAPHQL:
                body = {"data": {"repository": {"p4": Site.graphql(MERGED_PULLS[4])}}}
            elif request.full_url.startswith(SEARCH):
                body = {"total_count": 1, "incomplete_results": False, "items": [{"number": 4}]}
            else:
                body = []
            return mock.MagicMock(**{"__enter__.return_value.read.return_value": json.dumps(body).encode()})

        out = io.StringIO()
        with mock.patch.object(next_task.OPENER, "open", urlopen), \
                mock.patch.dict(os.environ, TOKEN, clear=True), redirect_stdout(out):
            self.assertEqual(next_task.main(["--json"]), 0)
        self.assertIn({"node_id": "Algebra/t6", "pull_requests": [4]}, json.loads(out.getvalue())["taken_by"])
        query = sent[-1]
        self.assertEqual((query.full_url, query.get_method()), (next_task.GRAPHQL, "POST"))
        self.assertEqual(query.get_header("Authorization"), "Bearer secret")
        self.assertEqual(query.get_header("Content-type"), "application/json")
        self.assertIn("p4: pullRequest(number: 4)", json.loads(query.data)["query"])

    def test_without_a_token_nothing_is_sent(self) -> None:
        # Nor is anything read past the open pull requests, as those merged since the list's commit need one.
        sent = self.requests({}, code=1)
        self.assertTrue(all(request.get_header("Authorization") is None for request in sent))
        self.assertEqual([request.full_url for request in sent], [next_task.TASKS, OPEN + "1"])

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


def node(node_id: str, page: object = "") -> dict:
    """A node to expand, as graph-tasks.json lists it."""
    return {"node_id": node_id, "title": f"Node {node_id}",
            "page": page if page != "" else f"roadmap/{node_id.rpartition('/')[0]}/index.html"}


GRAPH = {"schema": "atlas-graph-tasks/v1", "commit": TASKS["commit"], "commit_date": TASKS["commit_date"], "nodes": [
    node("Algebra/groups/sylow"),                  # its page's path is in an open pull request's body
    node("Algebra/groups/sylow-applications"),     # a longer id than the one a pull request gives
    node("Algebra/t1"),                            # its id is an open pull request's branch
    node("Algebra/t10"),
    node("Combinatorics/ramsey", page=7),          # a page that is not a text gives no link
]}
GRAPH_PULLS = [
    pull(20, "Expand the Sylow theorems", "Expands `blueprint/roadmap/Algebra/groups/sylow.md` into its parts."),
    pull(21, "Graph work", "", branch="expand/Algebra/t1"),
]


def graph_site(graph: dict | None = None, **kwargs) -> Site:
    site = Site(**kwargs)
    site.pages[next_task.GRAPH_TASKS] = json.dumps(GRAPH if graph is None else graph).encode()
    return site


class Graph(unittest.TestCase):
    def test_a_pull_request_takes_the_node_it_names_and_no_other(self) -> None:
        code, out, err = run(graph_site(open_pages=(OPEN_PULLS + GRAPH_PULLS,)), "--json", "--graph", "-n", "10",
                             env=TOKEN)
        self.assertEqual((code, err), (0, ""))
        result = json.loads(out)
        graph = result["graph"]
        self.assertEqual(graph["taken_by"], [{"node_id": "Algebra/groups/sylow", "pull_requests": [20]},
                                             {"node_id": "Algebra/t1", "pull_requests": [21]}])
        self.assertEqual([item["node_id"] for item in graph["next"]],
                         ["Algebra/groups/sylow-applications", "Algebra/t10", "Combinatorics/ramsey"])
        self.assertEqual((graph["to_expand"], graph["taken"], graph["free"]), (5, 2, 3))
        self.assertEqual(graph["next"][0], {
            "node_id": "Algebra/groups/sylow-applications", "title": "Node Algebra/groups/sylow-applications",
            "article_path": "blueprint/roadmap/Algebra/groups/sylow-applications.md",
            "page": "https://facebookresearch.github.io/atlas-lean/roadmap/Algebra/groups/index.html",
            "priority": 1})
        self.assertIsNone(graph["next"][2]["page"])
        # The ready tasks are listed as without --graph.
        self.assertEqual({key: value for key, value in result.items() if key != "graph"},
                         json.loads(run(Site(open_pages=(OPEN_PULLS + GRAPH_PULLS,)), "--json", "-n", "10",
                                        env=TOKEN)[1]))

    def test_an_expansion_merged_since_the_lists_commit_takes_its_node(self) -> None:
        merged = {**MERGED_PULLS, 22: pull(22, body="Expands Combinatorics/ramsey.", merged_at="2026-11-20T13:00:00Z"),
                  23: pull(23, body="Expands Algebra/t10.", merged_at="2026-11-20T11:00:00Z")}
        code, out, err = run(graph_site(merged=merged), "--json", "--graph", "-n", "10", env=TOKEN)
        self.assertEqual((code, err), (0, ""))
        graph = json.loads(out)["graph"]
        # #23 merged before the commit both lists come from, so the graph already shows its work.
        self.assertEqual(graph["taken_by"], [{"node_id": "Combinatorics/ramsey", "pull_requests": [22]}])

    def test_lists_from_two_builds_stop_the_script(self) -> None:
        for graph in (dict(GRAPH, commit="d" * 40), {key: value for key, value in GRAPH.items() if key != "commit"}):
            code, out, err = run(graph_site(graph), "--graph", env=TOKEN)
            self.assertEqual((code, out), (1, ""))
            self.assertIn("run this script again in a few minutes", err)
        # Nor does a task list without its commit date give a cutoff.
        tasks = {key: value for key, value in TASKS.items() if key != "commit_date"}
        site = graph_site(tasks=tasks)
        self.assertEqual(run(site, "--graph", env=TOKEN)[:2], (1, ""))
        self.assertEqual([url for url, _ in site.read], [next_task.TASKS, next_task.GRAPH_TASKS])

    def test_a_malformed_graph_list_stops_the_script(self) -> None:
        cases = [({}, "is not a list of nodes to expand"), (dict(GRAPH, schema="other"), "is not a list of nodes"),
                 (dict(GRAPH, nodes=[{"title": "no id"}]), "each with its node id"),
                 (dict(GRAPH, nodes=[node(" ")]), "each with its node id"),
                 (dict(GRAPH, nodes=[node("Algebra/a"), node("Algebra/a")]), "lists one node twice")]
        for graph, message in cases:
            code, out, err = run(graph_site(graph), "--graph", env=TOKEN)
            self.assertEqual((code, out), (1, ""), graph)
            self.assertIn(message, err, graph)

    def test_graph_reads_this_repositorys_pull_requests_only(self) -> None:
        site = graph_site()
        with self.assertRaises(SystemExit):
            run(site, "--graph", "--repo", "someone/fork", env=TOKEN)
        self.assertEqual(site.read, [])
        self.assertEqual(run(Site(), "--repo", REPO, env=TOKEN)[0], 0)

    def test_the_graph_comes_by_priority(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "priorities.json"
            path.write_text(json.dumps({"schema": next_task.PRIORITIES_SCHEMA, "default": 1,
                                        "weights": {"Combinatorics": 2, "Algebra/groups": 0.5}}))
            code, out, err = run(graph_site(), "--json", "--graph", "-n", "10", "--priorities", str(path), env=TOKEN)
        self.assertEqual((code, err), (0, ""))
        self.assertEqual([item["node_id"] for item in json.loads(out)["graph"]["next"]],
                         ["Combinatorics/ramsey", "Algebra/t1", "Algebra/t10", "Algebra/groups/sylow",
                          "Algebra/groups/sylow-applications"])

    def test_without_graph_the_graph_is_neither_read_nor_matched(self) -> None:
        site = graph_site()
        with mock.patch.object(next_task, "graph_taken") as matcher:
            code, out, _ = run(site, "--json", env=TOKEN)
        self.assertEqual(code, 0)
        self.assertNotIn("graph", json.loads(out))
        self.assertNotIn(next_task.GRAPH_TASKS, [url for url, _ in site.read])
        matcher.assert_not_called()

    def test_the_text_lists_the_nodes_to_expand(self) -> None:
        code, out, err = run(graph_site(open_pages=(OPEN_PULLS + GRAPH_PULLS,)), "--graph", "-n", "1", env=TOKEN)
        self.assertEqual((code, err), (0, ""))
        self.assertIn("5 nodes to expand; pull requests take 2 of them, so 3 are free.", out)
        self.assertIn("expand: Node Algebra/groups/sylow-applications", out)
        self.assertIn("Read its page's `## Expansion` section first", out)


if __name__ == "__main__":
    unittest.main()
