#!/usr/bin/env python3
"""Check whether a pull request is ready for the merge queue, and optionally queue it.

    python3 -I scripts/queue/preflight.py <PR> [--json] [--enqueue] [--max-age-hours H] [--max-files N]
        [--git-dir DIR]

Run main's copy, from a clean checkout of upstream main, never the copy on a pull request's branch:
a pull request may change this script, and it runs with your GitHub token. `-I` keeps Python from
importing modules from the script's directory or the environment. Its git commands ignore your
global git configuration: a proxy must come from the environment (https_proxy). When this file differs from
main's copy, or cannot be checked against it, it does not queue.

It prints READY or NOT READY, the reason for each failed check, and what to do next. It only reads,
unless --enqueue is given: then it queues the pull request with GitHub's `enqueuePullRequest`, pinned
to the head it checked (`expectedHeadOid`). It does so only if the verdict is READY, and only if
the following are unchanged since the check: main, the queue's entries and heads, the pull request,
and its approved Codex review. It sends that request once. When the outcome is unclear, it reads the
queue to report what happened. Exit status: 0 for READY (and
queued, with --enqueue), 1 for NOT READY or an enqueue that was refused or failed, 2 when the check
itself could not run.

Every merge group behind an entry contains that entry's change. If the change breaks the build, all
of those groups fail until GitHub removes it, which it does only once every entry ahead of it has
merged. Each removal restarts every build behind it. The checks, in order:

1. State: the pull request is open, targets main, is not a draft, is not queued already, and GitHub
   has found it mergeable.
2. Codex: the latest formal Codex review of the exact head approves it.
   - Codex posts that review as github-actions on the commit, a login that every workflow shares. So
     the Codex run that posted it must also print the review's id in its codex-verdict job, as
     codex.yml has it do.
   - For an automatic review, that job is a check on the head. For a review that a `@codex` comment
     asked for, or a fork's automatic review (a pull_request_target run), the run's checks attach to
     another commit, so it is looked up among the runs of that event.
   - When the pull request changes codex.yml, only a run that used main's workflow counts: a fork's
     automatic run, or the run of a `@codex` comment in the conversation. A comment on a line of the
     diff, like a same-repository automatic run, uses the changed workflow.
   - No other reviewer's latest review may request changes.
3. Required checks: every check that main's rules require passed on the head, in its latest run,
   reported by the app the rules name. Advisory checks are never waited for; a failed one is a
   warning.
4. Freshness: the checkout log of the CI run behind the head's `build` names the main commit it
   merged the head into. That commit must contain the newest main commit to change lean-toolchain,
   lake-manifest.json or lakefile.toml. No queued pull request ahead may change those files, and the
   run must be less than --max-age-hours old (6 by default). Otherwise, merge main into the branch
   and wait for CI and Codex.
5. Conflicts: main, then the head of every queued pull request in queue order, then this one,
   merged with `git merge-tree --write-tree` the way the queue builds its merge groups. A queued
   pull request that conflicts with the entries ahead of it is left out, as the queue removes it.
   But it stays if the entries it conflicts with leave first, and the entries behind then merge on
   top. So this one must also merge with the queue without each combination of those entries'
   blockers. The check fails for a left-out entry that no such queue keeps, and for more than 5
   left-out entries.
6. Duplicate declarations: the public names that merging this pull request adds to, or moves
   into, a file of MathlibExt, CSLibExt, PhyslibExt, Domains or WantedExt.
   - Such a name counts when the merged tree also declares it in a file that main changed since the
     CI run, or that a queued pull request changes, or twice in one file.
   - Names are qualified with their enclosing namespaces. In a `module` file only public
     declarations count.
   - It reads the merge onto the whole queue. If the pull request conflicts with an entry, it reads
     the merge onto the entries ahead of that one. It also reads the merges onto the queue without
     the blockers of left-out entries (see 5).
   - Reading merged trees covers what the merge does to the other side's files, such as a rename or
     a changed namespace.
   - Names that Lean generates count too: the fields, constructor and `toParent` projections of a
     structure or class, an inductive's constructors, those of `@[to_additive foo]`, `@[reassoc]`,
     `@[elementwise]` and `@[ext]` on a structure, and an anonymous instance's name, approximated from
     its class and types. Two new
     anonymous instances of one class in one namespace count as a possible collision. The names that
     `@[to_additive]` without a name, `@[simps]` and similar attributes generate cannot be predicted:
     they leave the check incomplete.
   - CI imports those libraries together, so a name declared twice fails the merge group that
     brings in the second. The CI run's own build already compared the head with main up to its
     base.

Evidence that cannot be read never passes. That covers the CI run's log, main's rules, a queue of
more than 500 entries, more than ten pages of reviews or checks, and a main that changed more than
3,000 library files since the CI run. Each makes its check fail or the run stop.

Warnings do not block. They advise queueing at a quiet hour, when few entries would rebuild behind a
failure. They cover:
- a change to a hub module, one that about 1,900 modules import;
- a change to a module that takes minutes to build;
- more than --max-files changed files (50 by default);
- a change to the pins or to a workflow;
- failed advisory checks;
- a heavy rebuild: a CI run over 45 minutes, or over three times the median of recent ones, which every
  merge group behind it repeats.

Why 6 hours. Of the 322 pull requests that landed on 23 November 2026 between 06:00 and 20:00 UTC:
- 75% were last queued within 2.7 hours of the push of their final head, so the limit leaves the
  usual flow alone;
- 72 were last queued more than 6 hours after it, nearly all of them work pushed overnight;
- main took about 140 merges in 6 hours (23 an hour that day);
- one head was queued behind the v4.36.0 bump with CI from the day before.
Refreshing a head costs a CI run of 10 to 15 minutes and a Codex review. An entry that breaks the
build in the queue makes every merge group behind it fail until it is removed.

GitHub is read with GH_TOKEN or GITHUB_TOKEN. Without them it uses `gh auth token`, else the active
github.com account in gh's hosts.yml.

Git work runs in a bare blobless clone with full history, created on first use under
$XDG_CACHE_HOME/atlas-lean-preflight (default ~/.cache). A shallow clone finds false conflicts on old
branches, because it misses their merge bases. Runs on one machine take turns on the clone, from
reading the queue to queueing. Before queueing, a run reads main and the queue again and stops if
either changed. Runs on different machines can still race in the seconds between that read and the
enqueue.

It needs git 2.45 or later and network access to github.com; set https_proxy if your network needs a
proxy. A check reads about a dozen API endpoints.
"""
from __future__ import annotations

import argparse
import collections
import contextlib
import datetime as dt
import fnmatch
import hashlib
import http.client
import itertools
import json
import math
import os
import re
import shlex
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

REPO = "facebookresearch/atlas-lean"
API = "https://api.github.com"
PIN_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
CI_CHECK = "build"
CI_WORKFLOW = ".github/workflows/ci.yml"
ACTIONS_APP_ID = 15368  # GitHub Actions
CODEX_WORKFLOW = ".github/workflows/codex.yml"
CODEX_LOGIN = "github-actions[bot]"
CODEX_FORMAL = ("<!-- codex-automatic-review -->", "<!-- codex-comment-review -->")
DEFAULT_MAX_AGE_HOURS = 6.0
# A build this long, or this many times the recent median, is a heavy rebuild: every merge group behind
# the pull request includes its changes, so each waits for that rebuild and does it again.
HEAVY_BUILD_MINUTES = 45
HEAVY_BUILD_FACTOR = 3
BUILD_SAMPLE = 20
DEFAULT_MAX_FILES = 50
MAX_QUEUE_PAGES = 5  # of 100 entries
MAX_MAIN_CHANGES = 3000
MAX_LEFT_OUT = 5  # queued entries left out for a conflict whose alternatives are explored
MAX_BLOB_BYTES = 8 << 20  # the largest Lean file in the libraries is about 0.4 MB
MAX_FILES_READ = 20000  # library files whose declarations one change set may need
MAX_BLOBS_BYTES = 512 << 20
# The libraries that CI's declaration-collision check imports together (scripts/list_v2_modules.sh).
# Test modules are built one by one, so two of them may declare the same name.
LIBRARIES = ("MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt")
LEAN_PATHSPEC = tuple(f":(glob){library}/**/*.lean" for library in LIBRARIES)  # every module, however nested
ZERO_OID = "0" * 40
EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
# Modules that about 1,900 other modules import: a change to one's interface rebuilds them in every
# merge group behind it (measured 23 November 2026).
HUB_MODULES = (
    "MathlibExt/Computability/Complexity.lean",
    "MathlibExt/Computability/BinaryNatEncoding.lean",
    "CSLibExt/Computability/CookLevin.lean",
    "CSLibExt/Computability/Complexity/Defs.lean",
    "CSLibExt/Logics/Propositional/CNF/Basic.lean",
)
# Path prefixes of modules that take five minutes or more to build on a CI runner, or that ci.yml
# builds one at a time for memory ("Build memory-heavy modules one at a time").
HEAVY_MODULES = (
    "MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes",
    "MathlibExt/Combinatorics/Words/TernaryAbelianCubeFreeLowerBound",
    "MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion",
    "MathlibExtTest/Combinatorics/TensorNetwork/Grid",
    "MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid",
    "PhyslibExt/CondensedMatter/IsingModel/Sharpness/ClusterLowerBound",
    "MathlibExt/NumberTheory/Digits/HappySixMin",
)
REFRESH = "merge main into the branch, push, and wait for CI and Codex"


class Failure(Exception):
    """The check could not run (exit status 2)."""


def parse_time(value: str | None) -> dt.datetime | None:
    if not value:
        return None
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00"))


def iso(moment: dt.datetime) -> str:
    return moment.astimezone(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def short(sha: str | None) -> str:
    return (sha or "?")[:10]


def shown(value: object) -> str:
    """`value` as text that cannot steer a terminal: each character that is not printable, such as ESC
    or a line end (a file name may hold one), is written as its escape (`\\x1b`, `\\n`)."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii") for c in str(value))


# --------------------------------------------------------------------------------------------------
# GitHub


def read_token() -> str | None:
    for name in ("GH_TOKEN", "GITHUB_TOKEN"):
        if os.environ.get(name):
            return os.environ[name]
    try:
        out = subprocess.run(["gh", "auth", "token", "--hostname", "github.com"], capture_output=True,
                             text=True, timeout=20)
        if out.returncode == 0 and out.stdout.strip():
            return out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    config = Path(os.environ.get("GH_CONFIG_DIR") or Path.home() / ".config" / "gh") / "hosts.yml"
    try:
        return hosts_token(config.read_text())
    except OSError:
        return None


def hosts_token(text: str) -> str | None:
    """The token of the active github.com account in gh's hosts.yml, which needs only a YAML subset."""
    top: dict[str, str] = {}
    users: dict[str, str] = {}
    in_block, indent, section, user = False, None, None, None
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        depth = len(line) - len(line.lstrip())
        key, _, value = line.strip().partition(":")
        value = value.strip().strip("'\"")
        if depth == 0:
            in_block, indent = key == "github.com", None
        elif in_block:
            indent = depth if indent is None else indent
            if depth == indent:
                top[key], section, user = value, key, None
            elif section == "users" and not value:
                user = key
            elif section == "users" and user and key == "oauth_token":
                users[user] = value
    if top.get("oauth_token"):
        return top["oauth_token"]  # gh keeps the active account's token at the top of the block
    if top.get("user"):
        return users.get(top["user"])  # never another account's token
    return next(iter(users.values())) if len(users) == 1 else None


class GitHub:
    """A small GitHub REST and GraphQL client. Redirects never carry the token."""

    def __init__(self, token: str, repo: str = REPO):
        self.token = token
        self.repo = repo
        self.calls = 0
        self.opener = urllib.request.build_opener()

    def _open(self, method: str, url: str, body: dict | None = None, attempts: int = 3):
        data = None if body is None else json.dumps(body).encode()
        for attempt in range(attempts):
            request = urllib.request.Request(url, data=data, method=method)
            request.add_header("Accept", "application/vnd.github+json")
            request.add_header("X-GitHub-Api-Version", "2022-11-28")
            request.add_header("User-Agent", "atlas-lean-preflight")
            request.add_unredirected_header("Authorization", f"Bearer {self.token}")
            if data is not None:
                request.add_header("Content-Type", "application/json")
            self.calls += 1
            try:
                return self.opener.open(request, timeout=60)
            except urllib.error.HTTPError as error:
                if error.code >= 500 and attempt < attempts - 1:
                    time.sleep(2 * (attempt + 1))
                    continue
                body_text = error.read().decode(errors="replace")
                try:
                    body_text = json.loads(body_text).get("message") or body_text
                except (ValueError, AttributeError):
                    pass
                raise Failure(f"{method} {url.replace(API, '', 1)}: HTTP {error.code} {str(body_text)[:200]}") from None
            except OSError as error:  # a network error or a timeout
                if attempt < attempts - 1:
                    time.sleep(2 * (attempt + 1))
                    continue
                raise Failure(f"{method} {url.replace(API, '', 1)}: {error}") from None
        raise AssertionError("unreachable")

    def get(self, path: str):
        with self._open("GET", API + path) as response:
            return json.load(response)

    def paged(self, path: str, key: str | None = None, max_pages: int = 10) -> list:
        items: list = []
        url = API + path + ("&" if "?" in path else "?") + "per_page=100"
        for _ in range(max_pages):
            with self._open("GET", url) as response:
                page = json.load(response)
                link = response.headers.get("Link") or ""
            items.extend(page[key] if key else page)
            found = re.search(r'<([^>]+)>;\s*rel="next"', link)
            if not found:
                return items
            url = found.group(1)
        raise Failure(f"GET {path}: more than {max_pages} pages")

    def graphql(self, query: str, variables: dict, attempts: int = 3) -> dict:
        """Run a query; pass attempts=1 for a mutation, which must not be sent twice."""
        with self._open("POST", API + "/graphql", {"query": query, "variables": variables}, attempts) as response:
            return json.load(response)

    def read_log(self, job_id: int, pattern: re.Pattern, max_bytes: int = 4 << 20) -> re.Match | None:
        """Search a job's log for `pattern`, reading only as far as its first match."""
        with self._open("GET", f"{API}/repos/{self.repo}/actions/jobs/{job_id}/logs") as response:
            text, read = "", 0
            while read < max_bytes:
                chunk = response.read(1 << 16)
                if not chunk:
                    break
                read += len(chunk)
                text += chunk.decode("utf-8", errors="replace")
                found = pattern.search(text)
                if found:
                    return found
                text = text[-4096:]
        return None


QUEUE_QUERY = """
query($owner: String!, $name: String!, $branch: String!, $qualified: String!, $number: Int!, $after: String) {
  repository(owner: $owner, name: $name) {
    ref(qualifiedName: $qualified) { target { oid } }
    pullRequest(number: $number) { mergeQueueEntry { position state enqueuedAt } }
    mergeQueue(branch: $branch) {
      entries(first: 100, after: $after) {
        totalCount
        pageInfo { hasNextPage endCursor }
        nodes { position state enqueuedAt pullRequest { number headRefOid } }
      }
    }
  }
}
"""

ENQUEUE_MUTATION = """
mutation($id: ID!, $head: GitObjectID!) {
  enqueuePullRequest(input: {pullRequestId: $id, expectedHeadOid: $head}) {
    mergeQueueEntry { position state }
  }
}
"""


def graphql_data(answer: dict, what: str) -> dict:
    if answer.get("errors"):
        raise Failure(f"{what}: " + "; ".join(e.get("message", "?") for e in answer["errors"]))
    return answer.get("data") or {}


def get_pull(gh: GitHub, number: int, waits: tuple[float, ...] = (2, 4, 8)) -> dict:
    pr = gh.get(f"/repos/{gh.repo}/pulls/{number}")
    for wait in waits:
        if pr.get("state") != "open" or pr.get("mergeable") is not None:
            break
        time.sleep(wait)  # GitHub computes mergeability after the first read
        pr = gh.get(f"/repos/{gh.repo}/pulls/{number}")
    return pr


def get_queue(gh: GitHub, branch: str, number: int) -> dict:
    """The queue in order, this pull request's own entry if any, and the branch's tip, as one snapshot:
    the same in two complete reads."""
    previous = None
    for _ in range(5):  # two complete reads that agree, entry for entry: pages read apart may mix two states
        snapshot = _read_queue(gh, branch, number)
        key = snapshot and json.dumps([snapshot["main"], snapshot.get("own"),
                                       [(e["number"], e["head"], e.get("position")) for e in snapshot["entries"]]],
                                      sort_keys=True)
        if key and key == previous:
            return snapshot
        previous = key
    raise Failure("the merge queue changed while it was read; run preflight again")


def _read_queue(gh: GitHub, branch: str, number: int) -> dict | None:
    """One read of the queue, page by page; None if the pages disagree (the branch's tip, the count) or
    the entries are not one queue (positions 1 to n, each pull request once)."""
    owner, name = gh.repo.split("/", 1)
    entries, own, after, tip, total = [], None, None, None, None
    for _ in range(MAX_QUEUE_PAGES):
        data = graphql_data(gh.graphql(QUEUE_QUERY, {"owner": owner, "name": name, "branch": branch,
                                                     "qualified": f"refs/heads/{branch}", "number": number,
                                                     "after": after}), "merge queue")
        repository = data.get("repository") or {}
        own = ((repository.get("pullRequest") or {}).get("mergeQueueEntry")) or own
        page_tip = ((repository.get("ref") or {}).get("target") or {}).get("oid")
        if tip is not None and page_tip != tip:
            return None  # main moved between pages
        tip = page_tip
        queue = repository.get("mergeQueue")
        if not queue:
            break
        page = queue["entries"]
        if total is not None and page.get("totalCount") != total:
            return None  # the queue changed between pages
        total = page.get("totalCount")
        for node in page["nodes"]:
            pull = node.get("pullRequest") or {}
            entries.append({"number": pull.get("number"), "head": pull.get("headRefOid"),
                            "position": node.get("position"), "state": node.get("state"),
                            "enqueued_at": node.get("enqueuedAt")})
        if not page["pageInfo"]["hasNextPage"]:
            break
        after = page["pageInfo"]["endCursor"]
    else:
        raise Failure(f"the merge queue has more than {MAX_QUEUE_PAGES * 100} entries")
    entries.sort(key=lambda e: e["position"] or 0)
    numbers = [e["number"] for e in entries]
    if (total is not None and len(entries) != total) or len(set(numbers)) != len(numbers) \
            or [e["position"] for e in entries] != list(range(1, len(entries) + 1)):
        return None
    return {"entries": entries, "own": own, "main": tip}


def get_required(gh: GitHub, branch: str) -> list[dict]:
    """The checks that the branch's rules require, each with the app that must report it."""
    required: list[dict] = []
    for rule in gh.paged(f"/repos/{gh.repo}/rules/branches/{urllib.parse.quote(branch)}"):
        if rule.get("type") == "required_status_checks":
            for check in (rule.get("parameters") or {}).get("required_status_checks") or []:
                requirement = {"context": check["context"], "integration_id": check.get("integration_id")}
                if requirement not in required:
                    required.append(requirement)
    return required


def summarize_reviews(reviews: list[dict], head: str) -> dict:
    """The latest formal Codex review of `head`, and other reviewers whose latest review requests changes."""
    codex_head, codex_latest, latest_by_user = None, None, {}
    for review in sorted(reviews, key=lambda r: (r.get("submitted_at") or "", r.get("id") or 0)):
        login = (review.get("user") or {}).get("login") or ""
        state = review.get("state")
        if state not in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            continue
        entry = {"id": review.get("id"), "state": state, "commit": review.get("commit_id"),
                 "submitted_at": review.get("submitted_at"), "login": login}
        if login == CODEX_LOGIN:
            body = review.get("body") or ""
            if not any(marker in body for marker in CODEX_FORMAL):
                continue
            entry["kind"] = "comment" if "<!-- codex-comment-review -->" in body else "automatic"
            codex_latest = entry
            if review.get("commit_id") == head:
                codex_head = entry
        else:
            latest_by_user[login] = entry
    change_requests = [e for e in latest_by_user.values() if e["state"] == "CHANGES_REQUESTED"]
    return {"codex": codex_head, "codex_latest": codex_latest, "change_requests": change_requests}


DETAILS_URL = re.compile(r"/actions/runs/(\d+)/job/(\d+)")
VERDICT_LINE = re.compile(r"\dZ Codex approved review (\d+)\.")


def job_of(gh: GitHub, job_id: int, run_id: int, name: str) -> bool:
    """Whether GitHub lists job `job_id`, named `name`, under workflow run `run_id`."""
    try:
        job = gh.get(f"/repos/{gh.repo}/actions/jobs/{job_id}")
    except Failure:
        return False  # a job it cannot read proves nothing
    return job.get("run_id") == run_id and job.get("name") == name


def codex_attested(gh: GitHub, runs: list[dict], review_id: int, number: int | None = None,
                   base_ref: str = "main") -> str | None:
    """The event of the codex.yml run whose codex-verdict check on the head names review `review_id`
    in its log, if one does. The bot's login is shared by every workflow; codex.yml prints the id of
    the review it posted. The check run must be the job's own, and the run this pull request's against
    `base_ref` alone: another pull request with the same head, into another branch, runs its own
    codex.yml there."""
    verdicts = [r for r in runs if r.get("name") == "codex-verdict" and r.get("conclusion") == "success"
                and (r.get("app") or {}).get("id") == ACTIONS_APP_ID]
    for check in sorted(verdicts, key=lambda r: r.get("id") or 0, reverse=True)[:3]:
        found = DETAILS_URL.search(check.get("details_url") or "")
        if not found:
            continue
        run_id, job_id = int(found.group(1)), int(found.group(2))
        if check.get("id") is not None and check.get("id") != job_id:
            continue  # it only points at a job
        run = gh.get(f"/repos/{gh.repo}/actions/runs/{run_id}")
        if run.get("path") != CODEX_WORKFLOW or not job_of(gh, job_id, run_id, "codex-verdict"):
            continue
        if number is not None:
            associated = run.get("pull_requests") or []
            mine = [pr for pr in associated if pr.get("number") == number and (pr.get("base") or {}).get("ref") == base_ref]
            if not mine or len(mine) < len(associated):
                continue  # another pull request's run, or one that cannot be told apart from it
        try:
            line = gh.read_log(job_id, VERDICT_LINE)
        except Failure:
            continue
        if line and int(line.group(1)) == review_id:
            return run.get("event")
    return None


# Only a conversation comment's run counts: it runs main's codex.yml. A comment on a line of the diff runs
# the workflow of whichever pull request it is on, and GitHub lists no pull request for that run.
COMMENT_EVENTS = ("issue_comment",)


def codex_comment_attested(gh: GitHub, review: dict, budget: int = 8, events: tuple[str, ...] = COMMENT_EVENTS,
                           head: str | None = None) -> tuple[str | None, bool]:
    """(event, incomplete) for the Codex run of the `@codex` comment that asked for `review`: the event
    of the run whose codex-verdict job printed the review's id, if found, and whether the search ran out
    of budget first. Such runs attach their checks to the commit of the ref they ran on, not the head,
    so they are looked up among the successful codex.yml runs that comments started in the 50 minutes
    before the review (the job's limit is 40). A conversation comment (issue_comment) runs main's
    workflow; a comment on a line of the diff runs the workflow of the pull request it is on, so such
    a run counts only if it ran on `head`, this pull request's head: another pull request's workflow
    could print anything. With events=("pull_request_target",) it finds the automatic review of a
    fork's pull request, whose run uses main's workflow and also attaches its checks to main."""
    submitted = parse_time(review.get("submitted_at"))
    if not submitted:
        return None, False
    window = urllib.parse.quote(f"{iso(submitted - dt.timedelta(minutes=50))}..{iso(submitted + dt.timedelta(minutes=1))}")
    workflow = CODEX_WORKFLOW.rsplit("/", 1)[1]
    runs = []
    for event in events:
        runs += [r for r in gh.paged(f"/repos/{gh.repo}/actions/workflows/{workflow}/runs?event={event}"
                                     f"&status=success&created={window}", "workflow_runs", max_pages=2)
                 if r.get("path") == CODEX_WORKFLOW and r.get("event") == event
                 and (event != "pull_request_review_comment" or (head and r.get("head_sha") == head))]
    runs.sort(key=lambda r: r.get("created_at") or "", reverse=True)
    for run in runs[:budget]:
        for job in gh.get(f"/repos/{gh.repo}/actions/runs/{run['id']}/jobs?per_page=50").get("jobs") or []:
            if job.get("name") == "codex-verdict" and job.get("conclusion") == "success":
                try:
                    line = gh.read_log(job["id"], VERDICT_LINE)
                except Failure:
                    continue
                if line and int(line.group(1)) == review["id"]:
                    return run["event"], False
    return None, len(runs) > budget


_YAML_KEY = re.compile(r"""\s*(?:"([^"\\]*)"|'([^']*)'|([A-Za-z0-9_-]+)):(?:\s+(.*?))?\s*$""")


def _yaml_code(line: str) -> str:
    """`line` without a trailing comment: a `#` after a space, outside quotes."""
    quote = None
    for i, char in enumerate(line):
        if quote:
            quote = None if char == quote else quote
        elif char in "'\"":
            quote = char
        elif char == "#" and (i == 0 or line[i - 1].isspace()):
            return line[:i].rstrip()
    return line.rstrip()


def _job_names(text: str) -> list[str]:
    return _read_jobs(text)[0]


def _read_jobs(text: str) -> tuple[list[str], bool]:
    """The check names of the jobs in one workflow file, and whether it understood every job: each
    job's own `name:`, else its id. A job it cannot read in full (a flow mapping, a merge key, a name
    that is an expression, a block scalar or an alias, any property it does not understand) is left
    out, and the file is then not understood, so that its runs stay unknown. Reads only the layout
    GitHub's workflows use: `jobs:` at the left margin, job ids one level in."""
    names: list[str] = []
    in_jobs, job_indent, property_indent, job, name, broken = False, None, None, None, None, False
    understood, saw_jobs = True, False

    def finish() -> None:
        nonlocal understood
        if job is not None and not broken:
            names.append(job if name is None else name)
        elif broken:
            understood = False

    def key_of(found) -> str:
        return found.group(1) if found.group(1) is not None else found.group(2) if found.group(2) is not None \
            else found.group(3)

    for raw in text.splitlines():
        line = _yaml_code(raw)
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent == 0:
            finish()
            job, name, broken, job_indent, property_indent = None, None, False, None, None
            found = _YAML_KEY.match(line)
            in_jobs = bool(found) and key_of(found) == "jobs" and not found.group(4)
            saw_jobs = saw_jobs or in_jobs or (bool(found) and key_of(found) == "jobs")
            if found and key_of(found) == "jobs" and found.group(4):
                understood = False  # `jobs: {...}`
            continue
        if not in_jobs:
            continue
        if job_indent is None or indent <= job_indent:
            finish()
            found = _YAML_KEY.match(line)
            job_indent, property_indent, name = indent, None, None
            job = key_of(found) if found else None
            broken = not found or bool(found.group(4)) or job is None  # `guard: {...}` or worse
            continue
        if job is None:
            continue
        property_indent = property_indent or indent
        if indent != property_indent:
            continue  # inside a property: steps, with, env, ...
        found = _YAML_KEY.match(line)
        if not found:
            broken = True  # a property it cannot read, `<<: *defaults` among them
        elif key_of(found) == "name":
            value = found.group(4) or ""
            if len(value) > 1 and value[0] == value[-1] and value[0] in "'\"":
                value = value[1:-1]
            elif value[:1] in ("|", ">", "*", "&", "!", "{", "[", "'", '"'):
                value = ""  # a block scalar, an alias, an anchor, a tag, a flow value: not read here
            if value and "${{" not in value:
                name = value
            else:
                broken = True
    finish()
    return names, understood and saw_jobs  # an indented document, say, has no `jobs:` at the left margin


def workflow_jobs(git: "Git", commit: str) -> tuple[dict[str, set[str]], set[str]]:
    """Which workflow files at `commit` define a job of each check name, and the files with a job it
    could not read. A required check is authenticated by its workflow file, since a pull request can
    add a workflow with a job of the same name."""
    paths = [p for p in git.out("ls-tree", "-z", "--name-only", commit, ".github/workflows/").split("\0")
             if p.endswith((".yml", ".yaml"))]
    oids = {path: git.out("rev-parse", f"{commit}:{path}") for path in paths}
    git.prefetch(set(oids.values()))
    texts = git.blobs(set(oids.values()))
    jobs: dict[str, set[str]] = {}
    unreadable = set()
    for path, oid in oids.items():
        names, understood = _read_jobs(texts.get(oid, ""))
        for name in names:
            jobs.setdefault(name, set()).add(path)
        if not understood:
            unreadable.add(path)
    return jobs, unreadable


def workflow_roots(git: "Git", commit: str, paths: list[str]) -> list[str]:
    """The top-level directories of `commit` whose code the workflows at `paths` run: see
    workflow_code."""
    return code_roots(workflow_code(git, commit, paths), lambda entry: code_signature(git, commit, entry) is not None)


def code_roots(code: list[str], present: "Callable[[str], bool] | None" = None) -> list[str]:
    """The top-level directories that hold code the checks run (scripts, local actions, what a glob or a
    test discovery selects): a pull request changing a file there needs a maintainer. Files that the checks
    only read count for freshness alone."""
    return sorted({entry[len("glob:"):].split("/", 1)[0] if entry.startswith("glob:") else entry.split("/", 1)[0]
                   for entry in code if entry != "?incomplete" and (present is None or present(entry)) and (
                       entry.endswith("/") or re.search(_SCRIPT, entry)
                       or (entry.startswith(".github/") and not entry.startswith(".github/workflows/")))})


def workflow_code(git: "Git", commit: str, paths: list[str]) -> list[str]:
    """The files of `commit` that the workflows at `paths` refer to as code (scripts they run, local
    actions, and what they read under .github/, such as the revision of a checker they fetch): a pull
    request's runs use its own copy of those too. The pins (lean-toolchain, lake-manifest.json,
    lakefile.toml) are what CI tests, not what tests it, and are left to their own check."""
    top = {line.split("\t", 1)[1] for line in git.out("ls-tree", commit).splitlines()
           if line.split()[1:2] == ["tree"]}
    oids = {path: git.out("rev-parse", f"{commit}:{path}") for path in paths}
    git.prefetch(set(oids.values()))
    texts = git.blobs(set(oids.values()))
    code = set()
    for oid in oids.values():
        for found in re.finditer(r"(?<![\w/-])(?:\./)?((\.?[A-Za-z0-9_][\w.-]*)/[\w./-]+)", texts.get(oid, "")):
            path, root = found.group(1).rstrip("."), found.group(2)
            if (root in top or _file_name(path)) and not path.startswith(".github/workflows/"):
                code.add(path)  # code it runs, and files it reads, even those main lacks (see _code_closure)
    return sorted(_code_closure(git, commit, code))


_SCRIPT = r"\.(?:py|sh|bash|js|mjs|cjs|ts|rb|pl|lua)$"
_CONFIG = r"\.(?:json|toml|ya?ml|txt|cfg|ini)$"  # files that name the paths a check reads: followed, not run


def code_signature(git: "Git", commit: str, entry: str) -> str | None:
    """What `entry` of a check's code is at `commit`: a file's blob, a directory's tree (`dir/`), or for
    a glob (`glob:scripts/*.sh`, `*` within one directory, as the shell has it) the paths it matches and
    their blobs."""
    if entry in git.watched:  # the entries of this run: signed together, once per revision, and kept
        if commit not in git.signatures:
            listing = git.listing(commit)
            git.signatures[commit] = {e: _signature(listing, e) for e in git.watched}
        return git.signatures[commit][entry]
    return _signature(git.listing(commit), entry)


def _signature(listing: dict[str, str], entry: str) -> str | None:
    if entry.startswith("glob:"):
        pattern = entry[len("glob:"):]
        literal = re.split(r"[*?\[]", pattern, 1)[0]  # what every match starts with: most paths are skipped at once
        matches = sorted(f"{record}\t{path}" for path, record in listing.items()
                         if path.startswith(literal) and not record.split()[1] == "tree" and _glob_match(path, pattern))
        return hashlib.sha1("\n".join(matches).encode()).hexdigest()
    return listing.get(entry.rstrip("/"))  # a file's mode, type and blob (an executable bit counts), a directory's tree


def _glob_match(path: str, pattern: str) -> bool:
    """Whether the shell's glob `pattern` selects `path`: `*` within one directory."""
    return path.count("/") == pattern.count("/") and fnmatch.fnmatchcase(path, pattern)


def _file_name(ref: str) -> bool:
    """Whether `ref`, which the commit lacks, still reads as a repository file the checks may read once it
    exists: a name with an extension, under a directory that is no host (`github.com/...`), with no `..`,
    and no library module (scripts' tests name many of those that never exist)."""
    parts = ref.split("/")
    return (re.search(r"\.\w+$", ref) is not None and "." not in parts[0].lstrip(".") and ".." not in parts
            and parts[0] not in LIBRARIES and not ref.endswith(".lean"))


def _code_closure(git: "Git", commit: str, start: set[str], limit: int = 500) -> set[str]:
    """`start` and the scripts it runs, as far as their text says: paths from the repository's root,
    file names next to the script, and Python modules it imports from its own directory. A directory
    that it names below the top level (`unittest discover -s scripts/queue`), or that a glob selects
    from (`scripts/checks/*.sh`), counts whole, as `dir/`: what runs there is whatever it holds. Past
    `limit` files, `?incomplete` says the rest was not followed."""
    listing = set(git.out("ls-tree", "-r", "-z", "--name-only", commit).split("\0"))
    folders = {path.rsplit("/", 1)[0] for path in listing if "/" in path}
    folders |= {f.rsplit("/", i)[0] for f in list(folders) for i in range(1, f.count("/") + 1)}
    top = {path.split("/", 1)[0] for path in listing}
    code, frontier = set(start) & listing, set(start) & listing
    for action in [s.rstrip("/") for s in start if s.rstrip("/") in folders and s.startswith(".github/actions/")]:
        code.add(f"{action}/")  # `uses: ./.github/actions/x`: whatever it holds runs
        frontier |= {f"{action}/{name}" for name in ("action.yml", "action.yaml")} & listing
    code |= frontier
    scanned = set(frontier)
    reads = {path for path in set(start) - listing if path not in folders}  # named, though main lacks it now

    def input_file(ref: str) -> bool:  # a file the checks may read: one main has, or a file name it lacks
        if ref.endswith(".lean") and not ref.startswith(("scripts/", ".github/")):
            return False  # a module CI builds, not an input to its checks (an inventory may list thousands)
        return not ref.startswith(".github/workflows/") and (ref in listing or _file_name(ref) and ref not in folders)
    while frontier:
        oids = {path: git.out("rev-parse", f"{commit}:{path}") for path in frontier
                if re.search(_SCRIPT, path) or re.search(_CONFIG, path)}
        git.prefetch(set(oids.values()))
        texts = git.blobs(set(oids.values()))
        found = set()
        for path, oid in oids.items():
            text, here = texts.get(oid, ""), path.rsplit("/", 1)[0] if "/" in path else ""
            text = re.sub(r"\$\{?\w+\}?/", "", text).replace('"', " ").replace("'", " ")  # "$REPO_ROOT/scripts/x" is scripts/x
            for ref in (re.sub(r"^(?:\./)+", "", r) for r in re.findall(r"(?<![\w/-])((?:\./)*[\w.-]+(?:/[\w.*-]+)+)", text)):
                if "*" in ref and ref.split("/", 1)[0] not in LIBRARIES and ".." not in ref.split("/") \
                        and "." not in ref.split("/", 1)[0].lstrip(".") \
                        and not ref.endswith(".lean"):  # `scripts/*.sh`, `policies/*.json`: what it selects, and their content
                    reads.add(f"glob:{ref}")  # (a glob over the libraries would make every pull request stale)
                if "*" not in ref and input_file(ref):
                    reads.add(ref)  # a file it reads (a list, a pin set): its content is the check's too
                found |= {p for p in listing if _glob_match(p, ref)} if "*" in ref else {ref} & listing
            for name in re.findall(r"(?<![\w/.-])([\w-]+\.\w+)(?![\w/])", text):  # `README.md` in a manifest: at the root
                if name in listing:
                    reads.add(name)
                    found.add(name)
            if re.search(_CONFIG, path):
                continue  # a configuration file names paths; it runs nothing and imports nothing
            for folder in re.findall(r"(?:\bdiscover\s+(?:-s\s+)?|\bpytest\s+)(?:\./)?([\w.-]+(?:/[\w.-]+)+)", text):
                if folder.rstrip("/") in folders:  # test discovery: whatever tests it holds run
                    code.add(f"{folder.rstrip('/')}/")
            for name in re.findall(r"(?<![\w/.-])([\w-]+\.(?:sh|py|bash))\b", text):
                found |= {f"{here}/{name}" if here else name} & listing
            for module in re.findall(r"^\s*(?:from|import)\s+([A-Za-z_]\w*)", text, re.M):
                found |= {f"{here}/{module}.py" if here else f"{module}.py"} & listing
        frontier = {p for p in (found | reads) - code - scanned if not p.startswith(".github/workflows/")  # workflows: data
                    and p in listing and (re.search(_SCRIPT, p) or re.search(_CONFIG, p) or p.startswith(".github/"))}
        scanned |= frontier
        if len(code | reads | frontier) > limit:
            return code | reads | {"?incomplete"}  # not followed to the end
        code |= frontier
    return code | reads


class Provenance:
    """Whose GitHub Actions check runs on the head are: "ours" when the workflow run is a pull_request or
    pull_request_target run that GitHub lists with this pull request and this base, "foreign" when it
    lists only other pull requests or another base, else "unknown". Another pull request with the same
    head can have runs there too. GitHub lists no pull request for a fork's runs, and a fork's branch
    can back pull requests to different bases, so a fork's runs are unknown. With `workflows` (see
    workflow_jobs), a run from another workflow file than the one on main that defines the job is
    foreign, and a job that no workflow on main defines is unknown. At most `budget` workflow runs are
    read."""

    def __init__(self, gh: GitHub, number: int, base_ref: str, budget: int = 20,
                 workflows: dict[str, set[str]] | None = None, unreadable: set[str] | None = None):
        self.gh, self.number, self.base_ref = gh, number, base_ref
        self.budget, self.runs, self.workflows, self.unreadable = budget, {}, workflows, unreadable or set()

    def run(self, run_id: int) -> dict | None:
        if run_id not in self.runs:
            if len(self.runs) >= self.budget:
                return None
            try:
                self.runs[run_id] = self.gh.get(f"/repos/{self.gh.repo}/actions/runs/{run_id}")
            except Failure:
                self.runs[run_id] = None
        return self.runs[run_id]

    def whose(self, check: dict) -> str:
        if (check.get("app") or {}).get("id") != ACTIONS_APP_ID:
            return "ours"  # another app: nothing to tie it to a pull request
        found = DETAILS_URL.search(check.get("details_url") or "")
        if found and check.get("id") is not None and int(found.group(2)) != check.get("id"):
            return "foreign"  # an Actions job's check run carries the job's id: this one only points at a job
        run = self.run(int(found.group(1))) if found else None
        if not run:
            return "unknown"
        suite = (check.get("check_suite") or {}).get("id")
        if suite is not None and run.get("check_suite_id") is not None and suite != run.get("check_suite_id"):
            return "foreign"  # not in that run's check suite
        if self.workflows is not None:
            paths = self.workflows.get(check.get("name"))
            if not paths:
                return "unknown"  # no workflow on main defines that job
            path = (run.get("path") or "").split("@", 1)[0]
            if not path:
                return "unknown"  # nothing says which workflow it came from
            if path not in paths:  # a job of the same name in another workflow, which a pull request can add,
                return "unknown" if path in self.unreadable else "foreign"  # unless that file was not read in full
        if run.get("event") not in ("pull_request", "pull_request_target"):
            return "foreign"
        associated = run.get("pull_requests") or []
        if not associated:
            return "unknown"  # nothing says which pull request, or which base, it tested
        mine = [pr for pr in associated if pr.get("number") == self.number]
        if not mine:
            return "foreign"  # it lists only other pull requests
        if len(mine) < len(associated):
            return "unknown"  # another pull request has the same head: which one's run it is, is unknown
        bases = {(pr.get("base") or {}).get("ref") for pr in mine}
        return "ours" if bases == {self.base_ref} else "foreign"

    def ours(self, check: dict) -> bool:
        return self.whose(check) == "ours"

    def latest(self, checks: list[dict]) -> tuple[dict | None, str]:
        """The newest of `checks` that is not foreign, and whose it is; newest first, stopping there."""
        for check in sorted(checks, key=lambda c: c.get("id") or 0, reverse=True):
            whose = self.whose(check)
            if whose != "foreign":
                return check, whose
        return None, "none"


def summarize_checks(runs: list[dict], required: list[dict], statuses: list[dict] | None = None,
                     provenance: Provenance | None = None) -> dict:
    """The latest run of each required check from the app that must report it, skipping the runs of other
    pull requests (see Provenance), and the failed advisory checks. A latest run that cannot be tied to
    this pull request counts as not passed."""
    latest: dict = {}
    for run in runs:
        for key in (run.get("name"), (run.get("name"), (run.get("app") or {}).get("id"))):
            if key not in latest or (run.get("id") or 0) > (latest[key].get("id") or 0):
                latest[key] = run  # check run ids grow with time, also for a run that has not started
    result = []
    for check in required:
        context, app_id = check["context"], check.get("integration_id")
        candidates = [r for r in runs if r.get("name") == context and
                      (not app_id or (r.get("app") or {}).get("id") == app_id)]
        if provenance is None:
            run, whose = max(candidates, key=lambda r: r.get("id") or 0, default=None), "ours"
        else:
            run, whose = provenance.latest(candidates)
        if run and whose == "unknown":  # its outcome still counts against it; only a pass needs tying
            result.append({"name": context, "status": run.get("status"), "conclusion": run.get("conclusion"),
                           "provenance": "unknown", "url": run.get("html_url") or run.get("details_url")})
            continue
        if run:
            found = DETAILS_URL.search(run.get("details_url") or "")
            result.append({"name": context, "status": run.get("status"), "conclusion": run.get("conclusion"),
                           "run": int(found.group(1)) if found else None,
                           "url": run.get("html_url") or run.get("details_url"),
                           "started_at": run.get("started_at"), "completed_at": run.get("completed_at")})
            continue
        # A commit status names no app, so it can only stand in for a check that requires none.
        status = None if app_id else next((s for s in statuses or [] if s.get("context") == context), None)
        if status and status.get("state") != "pending":
            result.append({"name": context, "status": "completed", "conclusion": status.get("state"),
                           "url": status.get("target_url")})
        else:
            result.append({"name": context, "status": "in_progress" if status else None, "conclusion": None,
                           "url": None})
    covered = {c["context"] for c in required} | {"codex", "codex-verdict"}  # the codex check covers those
    advisory_failed = sorted({run["name"] for key, run in latest.items() if isinstance(key, str)
                              and key not in covered and run.get("conclusion") in ("failure", "timed_out")})
    return {"required": result, "advisory_failed": advisory_failed}


CHECKOUT_MERGE = re.compile(r"HEAD is now at [0-9a-f]+ Merge ([0-9a-f]{40}) into ([0-9a-f]{40})")


def ci_run(gh: GitHub, runs: list[dict], head: str, number: int | None = None, base_ref: str = "main",
           provenance: Provenance | None = None) -> dict | None:
    """The CI run behind the head's latest `build` check that is not another pull request's: when it
    ran, and on which main it merged the head."""
    builds = [r for r in runs if r.get("name") == CI_CHECK and (r.get("app") or {}).get("id") == ACTIONS_APP_ID]
    if provenance is None:
        build, whose = max(builds, key=lambda r: r.get("id") or 0, default=None), "ours"
    else:
        build, whose = provenance.latest(builds)
    if not build:
        return None
    if whose == "unknown":
        return {"run_id": None, "created_at": None, "base": None,
                "base_error": "its latest build cannot be tied to this pull request"}
    found = DETAILS_URL.search(build.get("details_url") or "")
    if not found:
        return {"run_id": None, "created_at": None, "base": None, "base_error": "the build check names no run"}
    run_id, job_id = int(found.group(1)), int(found.group(2))
    run = (provenance.run(run_id) if provenance else None) or gh.get(f"/repos/{gh.repo}/actions/runs/{run_id}")
    info = {"run_id": run_id, "job_id": job_id, "created_at": run.get("created_at"),
            "attempt": run.get("run_attempt"), "event": run.get("event"), "url": run.get("html_url"),
            "base": None, "base_error": None}
    if run.get("path") != CI_WORKFLOW or run.get("event") != "pull_request" or run.get("head_sha") != head:
        info["base_error"] = (f"its run was {run.get('path')} for {run.get('event')} on "
                              f"{short(run.get('head_sha'))}, not {CI_WORKFLOW} for this head")
        return info
    if not job_of(gh, job_id, run_id, CI_CHECK):
        info["base_error"] = f"its job {job_id} is not the {CI_CHECK} job of run {run_id}"
        return info
    associated = run.get("pull_requests") or []  # empty for a fork: GitHub does not say whose run it is
    if associated and number is not None:
        tested = {(pr.get("base") or {}).get("ref") for pr in associated if pr.get("number") == number}
        if not tested:
            others = ", ".join(f"#{pr.get('number')}" for pr in associated)
            info["base_error"] = f"its run is for {others}, not this pull request"
            return info
        also = [f"#{pr.get('number')}" for pr in associated if pr.get("number") != number]
        if also:  # pull requests with the same head: GitHub lists them all
            info["base_error"] = f"its run also lists {', '.join(also)}, so which pull request it ran for is unknown"
            return info
        if tested != {base_ref}:  # it ran before the pull request was retargeted
            info["base_error"] = f"its run tested it against {', '.join(sorted(map(str, tested)))}, not {base_ref}"
            return info
    try:
        merge = gh.read_log(job_id, CHECKOUT_MERGE)
    except Failure as error:
        info["base_error"] = f"its log could not be read ({error})"
        return info
    if not merge:
        info["base_error"] = "its log names no merge commit"
    elif merge.group(1) != head:
        info["base_error"] = f"its checkout merged {short(merge.group(1))}, not the head"
    else:
        info["base"] = merge.group(2)
    return info


# --------------------------------------------------------------------------------------------------
# Git


class Git:
    """The bare blobless clone that the conflict and duplicate checks run in."""

    def __init__(self, git_dir: Path, url: str):
        self.dir = git_dir
        self.url = url
        self.read: dict[str, int] = {}  # the size of each file read so far
        self.attr_source: bool | None = None  # whether this git has --attr-source
        self.lazy_guard: bool | None = None  # whether this git has --no-lazy-fetch
        self.attribute_base: tuple[str, dict[str, str]] | None = None  # see attributes
        self.size_oracle = None  # oids -> their sizes, from the remote, before downloading (see prefetch)
        self.admitted: dict[str, int] = {}  # the blobs this run has downloaded, or is about to, and their sizes
        self.listings: "collections.OrderedDict[str, dict[str, str]]" = collections.OrderedDict()  # see listing
        self.watched: frozenset = frozenset()  # the check code this run compares (see code_signature)
        self.signatures: dict[str, dict[str, str | None]] = {}  # revision -> watched entry -> signature
        # The trees it merges come from pull requests: their .gitattributes may name a merge driver.
        # Git reads no global or system configuration, where such a driver could be defined, and gets
        # no credentials; the repository is public.
        kept = {key: value for key, value in os.environ.items()
                if (not key.startswith("GIT_") or key in ("GIT_SSL_CAINFO", "GIT_SSL_CAPATH", "GIT_PROXY_SSL_CAINFO"))
                and not re.search(r"TOKEN|SECRET|PASSWORD|CREDENTIAL|ASKPASS", key.upper())}
        self.env = dict(kept, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_ATTR_NOSYSTEM="1",
                        # nor the user's attributes file, which git reads even without configuration
                        GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="core.attributesFile", GIT_CONFIG_VALUE_0=os.devnull,
                        GIT_TERMINAL_PROMPT="0",
                        GIT_AUTHOR_NAME="preflight", GIT_AUTHOR_EMAIL="preflight@localhost",
                        GIT_AUTHOR_DATE="1000000000 +0000", GIT_COMMITTER_NAME="preflight",
                        GIT_COMMITTER_EMAIL="preflight@localhost", GIT_COMMITTER_DATE="1000000000 +0000")

    def run(self, *args: str, input: str | None = None, check: bool = True) -> subprocess.CompletedProcess:
        process = subprocess.run(["git", "--git-dir", str(self.dir), *args], input=input, text=True,
                                 capture_output=True, env=self.env)
        if check and process.returncode != 0:
            raise Failure(f"git {' '.join(args[:3])}: {process.stderr.strip()[:500]}")
        return process

    def out(self, *args: str, input: str | None = None) -> str:
        return self.run(*args, input=input).stdout.strip()

    @contextlib.contextmanager
    def locked(self):
        """Let one run at a time use the clone, from reading the queue to queueing."""
        try:
            import fcntl
        except ImportError:  # not on Unix: run unlocked
            yield
            return
        self.dir.parent.mkdir(parents=True, exist_ok=True)
        with open(f"{self.dir}.lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            yield

    def ensure(self) -> None:
        if (self.dir / "HEAD").exists():
            if self.run("config", "--get", "preflight.managed", check=False).stdout.strip() != "true":
                raise Failure(f"{self.dir} exists and was not made by preflight.py; pass another --git-dir")
            if self.run("config", "--get", "remote.origin.url", check=False).stdout.strip() != self.url:
                raise Failure(f"{self.dir} is a clone of another repository; pass another --git-dir")
            if self.out("rev-parse", "--is-shallow-repository") == "true":
                raise Failure(f"{self.dir} is shallow; delete it so that preflight.py clones it again")
            self.check_attributes()
            return
        self.dir.parent.mkdir(parents=True, exist_ok=True)
        process = subprocess.run(["git", "clone", "--quiet", "--bare", "--no-tags", "--filter=blob:none", "--template=",
                                  self.url, str(self.dir)], text=True, capture_output=True, env=self.env)
        if process.returncode != 0:
            raise Failure(f"git clone {self.url}: {process.stderr.strip()[:500]}")
        self.check_attributes()
        self.run("config", "preflight.managed", "true")

    def check_attributes(self) -> None:
        """Refuse a clone whose own info/attributes would change how merges are simulated."""
        attributes = self.dir / "info" / "attributes"
        if attributes.exists() and attributes.read_text(errors="replace").strip():
            raise Failure(f"{attributes} would change how merges are simulated; empty it or pass another --git-dir")

    def fetch(self, refspecs: list[str]) -> None:
        self.run("fetch", "--quiet", "--no-tags", "--force", "--filter=blob:none", "origin", *refspecs)

    def rev_parse(self, ref: str) -> str | None:
        process = self.run("rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}", check=False)
        return process.stdout.strip() or None

    def is_ancestor(self, ancestor: str, descendant: str) -> bool:
        return self.run("merge-base", "--is-ancestor", ancestor, descendant, check=False).returncode == 0

    def merge_base(self, a: str, b: str) -> str | None:
        return self.run("merge-base", a, b, check=False).stdout.strip() or None

    def merge_tree(self, ours: str, theirs: str) -> dict:
        """Merge `theirs` into `ours` as GitHub would, with the .gitattributes of `ours` (a bare clone has
        none of its own), so that `-merge` or `merge=binary` count; no merge driver is configured."""
        if self.attr_source is None:  # --attr-source needs git 2.41
            self.attr_source = self.run("--attr-source=" + EMPTY_TREE, "version", check=False).returncode == 0
        if self.attr_source:
            prefix = [f"--attr-source={ours}"]
        elif any(path.rsplit("/", 1)[-1] == ".gitattributes"
                 for path in self.out("ls-tree", "-r", "-z", "--name-only", ours).split("\0")):
            raise Failure(f"{short(ours)} has .gitattributes, which this git cannot apply to a simulated merge; "
                          "use git 2.41 or later")
        else:
            prefix = []
        guard = ["--no-lazy-fetch"] if self.guarded() else []
        # What a merge reads, admitted by size first (see prefetch): the attributes of `ours`, which git would
        # skip unread with only a warning, and the three sides of each file that both sides change.
        attributes = self.attributes(ours)
        sides = set()
        for base in self.run("merge-base", "--all", ours, theirs, check=False).stdout.split():
            ours_changes = {path: (old, new) for old, new, path in self.diff_raw(base, ours, ())}
            for old, new, path in self.diff_raw(base, theirs, ()):
                if path in ours_changes:
                    sides |= {old, new, *ours_changes[path]}
        self.prefetch(attributes | sides)
        unread = [oid for oid in attributes if not self.present(oid)]
        if unread:
            raise Failure(f"{short(ours)} has a .gitattributes that preflight could not download ({unread[0]})")
        for _ in range(50):  # anything else a merge reads (renamed files): admitted by size, then merged again
            process = self.run(*guard, *prefix, "merge-tree", "--write-tree", "--name-only",
                               "--no-messages", "-z", ours, theirs, check=False)
            needed = {oid for oid in re.findall(r"\b[0-9a-f]{40}\b", process.stderr) if oid not in (ours, theirs)}
            if process.returncode in (0, 1) or not needed:
                break
            before = set(self.admitted)
            self.prefetch(needed)
            if not set(self.admitted) - before and self.size_oracle is not None:
                break  # nothing more admitted: fail below
        if process.returncode not in (0, 1):
            raise Failure(f"git merge-tree {short(ours)} {short(theirs)}: {process.stderr.strip()[:500]}")
        fields = [f for f in process.stdout.split("\0") if f]
        return {"clean": process.returncode == 0, "tree": fields[0], "files": fields[1:]}

    def commit_tree(self, tree: str, parents: list[str], message: str) -> str:
        args = ["commit-tree", tree, "-m", message]
        for parent in parents:
            args += ["-p", parent]
        return self.out(*args)

    def last_change(self, ref: str, paths: tuple[str, ...]) -> dict | None:
        line = self.out("log", "--first-parent", "-1", "--format=%H%x00%s", ref, "--", *paths)
        if not line:
            return None
        sha, subject = line.split("\0", 1)
        found = re.match(r"Merge pull request #(\d+)", subject)
        return {"commit": sha, "subject": subject, "pr": int(found.group(1)) if found else None}

    def root_oids(self, ref: str, paths: tuple[str, ...]) -> dict[str, str]:
        """The blob of each of `paths` (full paths from the root) at `ref`."""
        oids = {}
        for record in self.out("ls-tree", "-z", ref, "--", *paths).split("\0"):
            if record:
                meta, path = record.split("\t", 1)
                oids[path] = meta.split()[2]
        return oids

    def changed_files(self, a: str, b: str) -> list[str]:
        return [p for p in self.out("diff", "--name-only", "--no-renames", "-z", a, b).split("\0") if p]

    def diff_raw(self, a: str, b: str, pathspec: tuple[str, ...] = LEAN_PATHSPEC) -> list[tuple[str, str, str]]:
        """(old blob, new blob, path) for each changed file; a zero blob is an added or deleted side."""
        fields = self.out("diff", "--raw", "--no-renames", "-z", "--no-abbrev", a, b, "--", *pathspec).split("\0")
        changes = []
        for meta, path in zip(fields[0::2], fields[1::2]):
            parts = meta.split()
            if len(parts) >= 4:
                changes.append((parts[2], parts[3], path))
        return changes

    def guarded(self) -> bool:
        """Whether git commands here run without fetching missing objects on demand (--no-lazy-fetch, git
        2.45). With a size oracle they must: anything else would download unchecked files."""
        if self.lazy_guard is None:
            self.lazy_guard = self.run("--no-lazy-fetch", "version", check=False).returncode == 0
        if not self.lazy_guard and self.size_oracle is not None:
            raise Failure("this git would download files whose size preflight has not checked; use git 2.45 or later")
        return self.lazy_guard

    def listing(self, commit: str) -> dict[str, str]:
        """Every path of `commit` (a commit or a tree), directories too, with its mode, type and object. A
        tree of the whole repository is large: only the last two are kept (see code_signature)."""
        if commit in self.listings:
            self.listings.move_to_end(commit)
        else:
            records = self.run("ls-tree", "-r", "-t", "-z", commit, check=False).stdout.split("\0")
            self.listings[commit] = {r.split("\t", 1)[1]: r.split("\t", 1)[0] for r in records if "\t" in r}
            while len(self.listings) > 2:
                self.listings.popitem(last=False)
        return self.listings[commit]

    def attributes(self, tree: str) -> set[str]:
        """The .gitattributes blobs of `tree`: the first tree is listed once, later ones by their
        difference from it, not by listing every path of every merge."""
        if self.attribute_base is None:
            self.attribute_base = (tree, {r.split("\t", 1)[1]: r.split("\t", 1)[0].split()[2]
                                          for r in self.out("ls-tree", "-r", "-z", tree).split("\0")
                                          if "\t" in r and r.split("\t", 1)[1].rsplit("/", 1)[-1] == ".gitattributes"})
        base, current = self.attribute_base[0], dict(self.attribute_base[1])
        for _, new, path in self.diff_raw(base, tree, (":(glob)**/.gitattributes",)):
            if new == ZERO_OID:
                current.pop(path, None)
            else:
                current[path] = new
        return set(current.values())

    def present(self, oid: str) -> bool:
        """Whether `oid` is in the clone, without downloading it."""
        return subprocess.run(["git", "--git-dir", str(self.dir), "--no-lazy-fetch" if self.lazy_guard else "--no-pager",
                               "cat-file", "-e", oid], capture_output=True,
                              env=dict(self.env, GIT_NO_LAZY_FETCH="1")).returncode == 0

    def prefetch(self, oids: set[str]) -> None:
        """Download the missing blobs in one request instead of one request per blob. A pull request
        chooses these files: with `size_oracle` (the sizes GitHub reports, before anything is downloaded),
        none over MAX_BLOB_BYTES is fetched and the distinct files of the run may not pass
        MAX_BLOBS_BYTES."""
        if not set(oids) - {ZERO_OID}:
            return
        wanted = sorted(set(oids) - {ZERO_OID})
        if self.guarded():  # the wanted objects alone, none fetched to answer
            checked = subprocess.run(["git", "--git-dir", str(self.dir), "cat-file", "--batch-check=%(objectname)"],
                                     input="\n".join(wanted) + "\n", text=True, capture_output=True,
                                     env=dict(self.env, GIT_NO_LAZY_FETCH="1")).stdout
            have = {line.split()[0] for line in checked.splitlines() if line and not line.endswith(" missing")}
        else:  # an older git would fetch each missing object to answer: list what the clone has
            have = set(self.out("cat-file", "--batch-check=%(objectname)", "--batch-all-objects").split())
        missing = [oid for oid in wanted if oid not in have]
        if missing and self.size_oracle is not None:
            sizes = self.size_oracle(missing)
            # A size GitHub does not report is not downloaded either: what needs it then fails, closed.
            missing = [oid for oid in missing if sizes.get(oid) is not None and sizes[oid] <= MAX_BLOB_BYTES]
            planned = dict(self.admitted, **{oid: sizes[oid] for oid in missing})
            if sum(planned.values()) > MAX_BLOBS_BYTES:  # over every download of this run, reserved before it
                raise Failure(f"the files to download would add up to {sum(planned.values())} bytes, more than the "
                              f"{MAX_BLOBS_BYTES} that preflight downloads in one run")
            self.admitted = planned
        for start in range(0, len(missing), 5000):
            self.run("-c", "fetch.negotiationAlgorithm=noop", "fetch", "--quiet", "--no-tags",
                     "--no-write-fetch-head", "--recurse-submodules=no", "--filter=blob:none", "--stdin",
                     "origin", input="\n".join(missing[start:start + 5000]) + "\n")

    def blobs(self, oids: set[str]) -> dict[str, str]:
        """The texts of `oids`. A pull request chooses these files, so their sizes are checked before
        they are read: none may exceed MAX_BLOB_BYTES, nor the distinct files that one run reads
        MAX_BLOBS_BYTES. With a size oracle, that holds before anything is downloaded (see prefetch)."""
        wanted = sorted(oids - {ZERO_OID})
        if not wanted:
            return {}
        self.prefetch(set(wanted))  # bounded before downloading; then nothing is fetched on demand below
        quiet = dict(self.env, GIT_NO_LAZY_FETCH="1") if self.guarded() else self.env
        checked = subprocess.run(["git", "--git-dir", str(self.dir), "cat-file", "--batch-check=%(objectname) %(objectsize)"],
                                 input="\n".join(wanted) + "\n", text=True, capture_output=True, env=quiet)
        if checked.returncode != 0:  # an object it may not fetch: refused, closed
            raise Failure(f"git cat-file: an object is missing, or larger than the {MAX_BLOB_BYTES} bytes that "
                          f"preflight reads: {checked.stderr.strip()[:300]}")
        for line in checked.stdout.splitlines():
            oid, _, size = line.partition(" ")
            if not size.isdigit():  # "<oid> missing": never mistake it for an empty file
                raise Failure(f"git cat-file: object {oid} is missing, or larger than the {MAX_BLOB_BYTES} bytes "
                              "that preflight reads")
            if int(size) > MAX_BLOB_BYTES:
                raise Failure(f"object {oid} is {int(size)} bytes, more than the {MAX_BLOB_BYTES} that preflight reads")
            self.read[oid] = int(size)
        if sum(self.read.values()) > MAX_BLOBS_BYTES:  # over the distinct files that this run reads
            raise Failure(f"the files to read add up to {sum(self.read.values())} bytes, more than the "
                          f"{MAX_BLOBS_BYTES} that preflight reads in one run")
        process = subprocess.run(["git", "--git-dir", str(self.dir), "cat-file", "--batch"],
                                 input=("\n".join(wanted) + "\n").encode(), capture_output=True, env=quiet)
        if process.returncode != 0:
            raise Failure(f"git cat-file: {process.stderr.decode(errors='replace')[:500]}")
        data, pos, texts = process.stdout, 0, {}
        while pos < len(data):
            end = data.index(b"\n", pos)
            header = data[pos:end].decode().split()
            pos = end + 1
            if len(header) < 3:  # "<oid> missing": never mistake it for an empty file
                raise Failure(f"git cat-file: object {header[0]} is missing")
            size = int(header[2])
            texts[header[0]] = data[pos:pos + size].decode("utf-8", errors="replace")
            pos += size + 1
        return texts


# --------------------------------------------------------------------------------------------------
# Lean declarations

_TOP_LEVEL = re.compile(r'/-|--[^\n]*|(?<![\w.\'])r#*"|"(?:[^"\\]|\\[\s\S])*"|\'"\'|\'\\"\'')
_NESTED = re.compile(r"/-|-/")
_IN_PREFIX = re.compile(r"^(?:(?:(?:open|set_option|omit|include|variable|#guard_msgs|#count_heartbeats)\b.*?\bin|#time)\s+)+")
_WORD = re.compile(r"([A-Za-z_]+)\b\s*")
_MODIFIERS = {"private", "protected", "public", "noncomputable", "partial", "unsafe", "nonrec",
              "scoped", "local", "meta"}
_HELPER_PARENTS = {"theorem", "lemma", "def", "abbrev", "instance", "opaque", "irreducible_def"}
# The names Lean reserves for a definition's equations and induction principles, made when first used,
# perhaps in another module: f.eq_1, f.eq_2, ..., f.eq_def, f.eq_unfold, f.induct, ...
_RESERVED = re.compile(r"\.(?:eq_\d+|eq_def|eq_unfold|induct|induct_unfolding|mutual_induct|fun_cases|fun_cases_unfolding)$")
_NOT_HELPERS = {"termination_by", "decreasing_by", "deriving", "where"}
_LET_REC = re.compile(r"\blet\s+rec\s+")


def _let_recs(text: str) -> list[str | None]:
    """The names of the `let rec` functions in `text`, quote-aware (`«two words»`); None for one it
    cannot read."""
    return [_identifier(_skip_attributes(text[found.end():])[0].lstrip())  # `let rec @[reducible] go`
            for found in _LET_REC.finditer(text)]
_COMMANDS = None  # filled in below, once the command sets exist
_DECLARATIONS = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
                 "opaque", "axiom", "irreducible_def", "theorem_wanted", "proof_wanted", "def_wanted", "instance_wanted",
                 "alias"}
# Commands that declare a parser, or a constant, with a name of their own: `(name := x)` names it;
# otherwise Lean makes one up from the syntax, which preflight cannot predict.
_SYNTAX_COMMANDS = {"syntax", "macro", "elab", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
                    "macro_rules", "elab_rules", "declare_syntax_cat"}  # declare_syntax_cat C: Lean.Parser.Category.C
_INITIALIZERS = {"initialize", "builtin_initialize"}
_STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')


_ESCAPE = re.compile(r'\\(?:u([0-9a-fA-F]{4})|x([0-9a-fA-F]{2})|([nrt\\"\'])|\n\s*)')


def _unescape(literal: str) -> str:
    """A Lean string literal's value: `\\u0071` is `q`, `\\n` a line break, `\\` and a line end nothing."""
    plain = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", '"': '"', "'": "'"}
    return _ESCAPE.sub(lambda m: chr(int(m.group(1) or m.group(2), 16)) if (m.group(1) or m.group(2))
                       else plain[m.group(3)] if m.group(3) else "", literal)


def _parser_name(keyword: str, after: str) -> str | None:
    """The base of the name Lean gives a syntax command without `(name := ...)`, as `mkNameFromParserSyntax`
    does; Lean takes that base, or adds `_1`, `_2`, ... until the name is unused, which preflight
    cannot tell, so declarations() yields `?parser:<base>`:
    the category, then each string literal trimmed, with spaces as `_` and its first letter capitalised,
    and `_` for each category it refers to. Only for simple forms (literals, categories with a
    precedence, `x:cat` binders); None for anything else. `after` keeps the string contents."""
    text = re.sub(r"^\s*:\s*\w+", "", after)  # the command's own precedence, as in infixl:65
    while True:
        stripped = re.sub(r"^\s*\((?:name|priority|kind)\s*:=[^)]*\)", "", text)
        if stripped == text:
            break
        text = stripped
    if keyword == "syntax":
        found = re.fullmatch(r"(.*?)\s:\s*([A-Za-z_][\w.]*)\s*", text)
    elif keyword in ("macro", "elab"):
        found = re.fullmatch(r"(.*?)\s:\s*([A-Za-z_][\w.]*)\s*=>.*", text)
    elif keyword == "notation":
        found = re.fullmatch(r"(.*?)()=>.*", text)
    elif keyword in ("infix", "infixl", "infixr", "prefix", "postfix"):
        literal = re.fullmatch(r'\s*("(?:[^"\\]|\\.)*")\s*=>.*', text)
        if not literal:
            return None
        items = {"prefix": f"{literal.group(1)} x", "postfix": f"x {literal.group(1)}"}.get(keyword,
                                                                                         f"x {literal.group(1)} x")
        found = re.fullmatch(r"(.*)()", items)
    else:
        return None
    if not found:
        return None
    items, category = found.group(1), (found.group(2) or "term").split(".")[-1]
    name, rest = category, items
    while rest.strip():
        rest = rest.lstrip()
        literal = _STRING.match(rest)
        if literal:
            value = " ".join(_unescape(literal.group(1)).split()).replace(" ", "_")
            name += value[:1].upper() + value[1:]
            rest = rest[literal.end():]
            continue
        reference = re.match(r"(?:[A-Za-z_][\w']*:)?[A-Za-z_][\w.]*(?::(?:max|arg|lead|min|\d+))?", rest)
        if not reference:
            return None  # a combinator or a group: not a simple form
        name += "_"
        rest = rest[reference.end():]
    return name
# `<command> in <declaration>` on one line, for any command (`attribute [local instance] x in`,
# `local notation ... in`): what comes after an `in` that a declaration, a modifier or `@[` follows.
_SCOPED_IN = re.compile(r"^.*?\bin\s+(?=@\[|(?:%s)\b)" % "|".join(sorted(_DECLARATIONS | _MODIFIERS)))


_PLAIN = re.compile(r"[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪ]*\Z")
_KEYWORDS = None  # filled in below, once the keyword sets exist


def _canonical(name: str) -> str:
    """`name` as Lean prints it: `N.«dup»` is `N.dup`, while `«weird name»` and `«def»` keep their
    guillemets. Dots inside guillemets belong to the component."""
    parts, current, depth = [], "", 0
    for char in name:
        depth += (char == "«") - (char == "»")
        if char == "." and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += char
    parts.append(current)
    return ".".join(part[1:-1] if part[:1] == "«" and part[-1:] == "»" and _PLAIN.match(part[1:-1])
                    and part[1:-1] not in _KEYWORDS else part for part in parts)


def _component(text: str) -> str:
    """One name component as Lean prints it: `«...»` unless it is a plain identifier."""
    return text if _PLAIN.match(text) and text not in _KEYWORDS else f"«{text}»"


def _suffixed(name: str, suffix: str) -> str:
    """`name` with `suffix` added to its last component, as Lean names `N.«my.e»`'s `_apply` lemma
    `N.«my.e_apply»`."""
    prefix, last = _split_last(name)
    return (f"{prefix}." if prefix else "") + _component(last + suffix)


def _split_last(name: str) -> tuple[str, str]:
    """(prefix, last component without guillemets) of a canonical name."""
    if name.endswith("»") and "«" in name:
        start = name.rindex("«")
        return name[:start].rstrip("."), name[start + 1:-1]
    prefix, _, last = name.rpartition(".")
    return prefix, last


_SELECTOR = re.compile(r"\[\s*((?:«[^»]*»|[^\s.«»\[\]]+)(?:\.(?:«[^»]*»|[^\s.«»\[\]]+))*)\s*\]\s*")
_SCOPE_NAME = re.compile(r"\s*((?:«[^»]*»|[^\s.«»()\[\]{},:]+)(?:\.(?:«[^»]*»|[^\s.«»()\[\]{},:]+))*)")


def _blank(text: str) -> str:
    return re.sub(r"[^\n]", " ", text)


def strip_comments(text: str, keep_strings: bool = False) -> str:
    """Blank out comments (nested block comments included) and, unless `keep_strings`, the contents of
    strings, keeping every line where it was."""
    out, pos = [], 0
    while pos < len(text):
        found = _TOP_LEVEL.search(text, pos)
        if not found:
            out.append(text[pos:])
            break
        out.append(text[pos:found.start()])
        token = found.group()
        if token.startswith("--"):
            out.append(" " * len(token))
            pos = found.end()
        elif token.startswith('"'):
            out.append(token if keep_strings else '"' + _blank(token[1:-1]) + '"')
            pos = found.end()
        elif token.startswith("r"):  # a raw string r"..." or r#"..."#, which no escape ends
            closing = '"' + token[1:-1]
            end = text.find(closing, found.end())
            end = len(text) if end < 0 else end
            content = text[found.end():end]
            out.append(token + (content if keep_strings else _blank(content)) + text[end:end + len(closing)])
            pos = end + len(closing)
        elif token != "/-":
            out.append(token)  # the character literal '"'
            pos = found.end()
        else:
            depth, end = 1, found.end()
            while depth:
                nested = _NESTED.search(text, end)
                if not nested:
                    end = len(text)
                    break
                depth += 1 if nested.group() == "/-" else -1
                end = nested.end()
            out.append(_blank(text[found.start():end]))
            pos = end
    return "".join(out)


def _skip_attributes(line: str, depth: int = 0) -> tuple[str, int]:
    """Drop the attributes `@[...]` that start `line`, and the rest of one that an earlier line opened
    (`depth` brackets still open). Returns what follows and the brackets left open."""
    rest = line
    while True:
        if depth == 0:
            rest = rest.lstrip()
            if not rest.startswith("@["):
                return rest, 0
            depth, rest = 1, rest[2:]
        for index, char in enumerate(rest):
            depth += char == "["
            depth -= char == "]"
            if depth == 0:
                rest = rest[index + 1:]
                break
        else:
            return "", depth


def _identifier(text: str) -> str | None:
    out, index = [], 0
    while index < len(text):
        char = text[index]
        if char == "«":
            end = text.find("»", index)
            if end < 0:
                return None
            out.append(text[index:end + 1])
            index = end + 1
        elif char.isspace() or char in ":([{⦃⟨|,;)=" or text.startswith(".{", index):
            break
        else:
            out.append(char)
            index += 1
    name = "".join(out).rstrip(".")
    if not name or not (name[0].isalpha() or name[0] in "_«"):
        return None
    return name


def _declared_names(keyword: str, rest: str) -> list[str]:
    """The names a declaration introduces: one, or each named direction of `alias ⟨mp, mpr⟩ := …`."""
    rest = rest.lstrip()
    if keyword == "alias" and rest.startswith("⟨"):
        inner = rest[1:rest.find("⟩")] if "⟩" in rest else rest[1:]
        return [name for name in (_identifier(part.strip()) for part in inner.split(",")) if name and name != "_"]
    name = _declared_name(keyword, rest)
    return [name] if name else []


def _declared_name(keyword: str, rest: str) -> str | None:
    rest = rest.lstrip()
    if keyword == "instance":
        if rest.startswith("(priority"):
            depth = 0
            for index, char in enumerate(rest):
                depth += char == "("
                depth -= char == ")"
                if depth == 0:
                    rest = rest[index + 1:].lstrip()
                    break
        if not rest or rest[0] in ":([{⦃⟨" or rest.startswith("where"):
            return None  # an anonymous instance gets a generated name
    return _identifier(rest)


_NOTATION = {"ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat", "ℝ": "Real", "ℂ": "Complex"}
_UNPREDICTABLE = ("simps", "mk_iff", "to_dual", "to_app")
_SUFFIXES = {"reassoc": "_assoc", "elementwise": "_apply"}  # the lemma that each attribute adds


_CLOSING = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}


def _instance_type(rest: str) -> str | None:
    """The type after an anonymous instance's binders and top-level colon, if this text has it."""
    text = rest.lstrip()
    while text and text[0] in _CLOSING:
        opening, depth = text[0], 0
        for index, char in enumerate(text):
            depth += (char == opening) - (char == _CLOSING[opening])
            if depth == 0:
                text = text[index + 1:].lstrip()
                break
        else:
            return None
    return text[1:] if text.startswith(":") else None


def _generated(keyword: str, names: list[str], rest: str, attributes: str, qualify) -> list[str]:
    """Names that Lean or Mathlib generate for a declaration, as far as preflight can tell.

    `@[to_additive foo]` adds `foo`, `@[reassoc]` adds `_assoc` and `@[elementwise]` `_apply` to the
    name, `@[ext]` on a structure adds `.ext` and `.ext_iff`, and an anonymous instance gets a name made
    of the class and the types, approximated here. It also yields
    `?inst:<namespace>:<class>` for an anonymous instance, which matches another anonymous instance of
    the class in the namespace, and `?gen:<attribute>:<name>` for names it cannot predict."""
    out = []
    additive = re.search(r"\bto_additive\b((?:\s*\([^)]*\))*)\s*([^\s\]\"(),]*)", attributes)
    if additive and additive.group(2) != "existing":
        explicit = _identifier(additive.group(2)) if additive.group(2) else None
        out += [qualify(explicit)] if explicit else [f"?gen:to_additive:{n}" for n in names or ["instance"]]
        if explicit:  # `@[to_additive (attr := reassoc, simps) addFoo]`: the additive copy has them too
            for attribute, suffix in _SUFFIXES.items():
                if re.search(rf"\b{attribute}\b", attributes):
                    out.append(_suffixed(qualify(explicit), suffix))
            for attribute in _UNPREDICTABLE:
                if re.search(rf"\b{attribute}\b", attributes):
                    out.append(f"?gen:{attribute}:{qualify(explicit)}")
    for attribute in _UNPREDICTABLE:
        if re.search(rf"\b{attribute}\b", attributes):
            out += [f"?gen:{attribute}:{n}" for n in names or ["instance"]]
    for attribute, suffix in _SUFFIXES.items():
        if re.search(rf"\b{attribute}\b", attributes):
            out += [_suffixed(n, suffix) for n in names]
    if keyword in ("structure", "class") and re.search(r"\bext\b", attributes):
        out += [suffix for n in names for suffix in (f"{n}.ext", f"{n}.ext_iff")]
    if keyword == "instance" and not names:
        kind = re.split(r":=|\bwhere\b|\|", _instance_type(rest) or "")[0]
        tokens = re.findall(r"[A-Za-z_ℕℤℚℝℂ][\w.'ℕℤℚℝℂ]*", kind)
        heads = [_NOTATION.get(t, t).rstrip(".").split(".")[-1] for t in tokens if t[0].isupper() or t in _NOTATION]
        if heads:
            out.append(qualify("inst" + "".join(h[0].upper() + h[1:] for h in heads)))
        namespace = qualify("x")[:-1].rstrip(".")
        out.append(f"?inst:{namespace}:{heads[0] if heads else '*'}")
    return out


_CONSTRUCTOR = re.compile(r"([^\s:()\[\]{}|]+)\s*::")
_TERM_KEYWORDS = {"fun", "λ", "let", "have", "show", "if", "then", "else", "match", "with", "do", "by", "at", "from",
                  "forall", "exists", "Type", "Sort", "Prop"}
_KEYWORDS = _TERM_KEYWORDS | _DECLARATIONS | _MODIFIERS | {"namespace", "section", "end", "where", "in", "open",
                                                           "variable", "universe", "deriving", "mutual", "import"}
# Commands that declare nothing, beside those it reads; any other command at the left margin (a macro, a
# `run_cmd`, `register_grind_attr`, ...) may expand to declarations, so it makes the check incomplete.
_HARMLESS = {"add_decl_doc", "assert_not_exists", "assert_not_imported", "compile_inductive", "suppress_compilation",
             "unseal", "seal", "library_note", "initialize_simps_projections",
             # nor are these, which go on a definition or a proof at the left margin
             "termination_by", "decreasing_by", "where", "with"}
# `#` commands that declare nothing; any other at command level may be a macro that does.
_HARMLESS_HASH = {"#print", "#check", "#eval", "#reduce", "#exit", "#lint", "#guard_msgs", "#guard", "#guard_expr",
                  "#help", "#synth", "#find", "#where", "#align", "#align_import", "#noalign", "#adaptation_note",
                  "#simp", "#norm_num", "#conv", "#whnf", "#version", "#min_imports",
                  "#import_path", "#find_home", "#explode", "#widget", "#html", "#sample", "#long_names", "#leansearch",
                  "#loogle", "#check_failure", "#discr_tree_key", "#discr_tree_simp_key", "#unfold?", "#push_neg",
                  "#instances", "#kernel_reduce", "#show_unused", "#help_tactic", "#test"}
_OPEN_END = re.compile(r"(?::|\bby|=>|↦|←|→|↔|,|[(\[{⟨=+\-*/∧∨<>≤≥≠∘•·∈∉⊆⊂×^%|$]|"
                       r"\b(?:with|then|else|do|from|at|fun|λ|have|show|calc|in|if|match|let))\s*$")
_CONTINUATION = re.compile(r"\s*[=:,)\]}|+*/<>≤≥≠∘•·∈∉⊆⊂∧∨→↔×^%-]")  # a bare word may be a command too
_AGAIN = re.compile(r"(?<![\w.'@\[])(?:(" + "|".join(sorted(_DECLARATIONS | {"namespace", "section"}, key=len, reverse=True))
                    + r")\s+[^\s:=]|(end)(?=\s|$))")
_COMMANDS = _DECLARATIONS | _INITIALIZERS | _SYNTAX_COMMANDS | {
    "namespace", "section", "end", "mutual", "deriving", "example", "open", "variable", "universe", "attribute",
    "set_option", "omit", "include", "export", "import", "module", "noncomputable", "elab_rules", "macro_rules"}
_WHERE = re.compile(r"\bwhere\b")


def _skip_binders(text: str) -> str | None:
    """`text` after the balanced binder groups that start it, or None if one does not close."""
    text = text.lstrip()
    while text and text[0] in _CLOSING:
        opening, depth = text[0], 0
        for index, char in enumerate(text):
            depth += (char == opening) - (char == _CLOSING[opening])
            if depth == 0:
                text = text[index + 1:].lstrip()
                break
        else:
            return None
    return text


def _field_names(line: str) -> list[str] | None:
    """The fields that a structure's field line declares (`x y : T`, `f (n : Nat) : T`, `(x : T)`,
    `protected x : T`), a private one as `?local:x` (it clashes only in its file), or None if the line is
    not a field."""
    text = line.strip()
    visibility = re.match(r"(private|protected)\s+", text)
    if visibility:
        text = text[visibility.end():]
    if text[:1] in _CLOSING:  # binder style: (x y : T)
        inner = text[1:]
        names = inner.split(":", 1)[0].split() if ":" in inner else []
    else:
        names, rest = [], text
        while True:
            word = re.match(r"([^\s:()\[\]{}⦃⦄]+)\s*", rest)
            if not word or not _identifier(word.group(1)):
                break
            names.append(word.group(1))
            rest = rest[word.end():]
        after = _skip_binders(rest) if names else ""
        binders = rest.lstrip()[:1] in _CLOSING
        # A field's binders, or its type, may go on over the next lines.
        if not names or not (after is None or (binders and not after) or
                             (after.startswith(":") and not after.startswith(":="))):
            return None
    if not names or not all(_identifier(name) and name not in _TERM_KEYWORDS for name in names):
        return None
    if _another_field(text):  # `x : Nat y : Bool`: more than it reads
        return None
    return [f"?local:{name}" for name in names] if visibility and visibility.group(1) == "private" else names


def _another_field(text: str) -> bool:
    """Whether a field line goes on to another field after its first group's type: a second binder
    group, or a second colon outside brackets and binders (`∀ x : T, ...`, `fun x : T => ...`). A default
    value (`:= ...`) ends the reading: it may be any term."""
    depth, groups, colons, binder = 0, 0, 0, False
    bracketed = text.lstrip()[:1] in "([{⦃"
    for index, char in enumerate(text):
        if bracketed and depth == 0 and groups and not char.isspace():
            return True  # `(a : Nat) x : Nat`, `(a : Nat) (b : Nat)`: a second field after the first group
        if char in "([{⦃⟨":
            groups += depth == 0
            depth += 1
        elif char in ")]}⦄⟩":
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", index):
                break
            if char == ":" and not text.startswith("::", index) and text[index - 1:index] != ":":
                colons += not binder
            elif char in ",↦" or text.startswith("=>", index):
                binder = False
            elif _BINDER.match(text, index):
                binder = True
    return colons > 1


_BINDER = re.compile(r"[∀∃λΠΣ∑∏⨆⨅⋃⋂∫]|\b(?:fun|forall|exists)\b")


def _parents(rest: str) -> list[str]:
    """The projections to the structures that `extends` names: `toParent`, or the name a clause gives it
    (`extends part : Parent`)."""
    clause = re.search(r"\bextends\b(.*?)(?:\bwhere\b|:=|$)", rest)
    if not clause:
        return []
    projections: list[str | None] = []  # None: a parent whose projection's name it cannot tell
    parts, depth, start = [], 0, 0
    text = clause.group(1)
    for index, char in enumerate(text):  # the clauses, split at top-level commas
        depth += char in "([{⟨" and 1 or (-1 if char in ")]}⟩" else 0)
        if char == "," and depth == 0:
            parts.append(text[start:index])
            start = index + 1
    parts.append(text[start:])
    for part in (p.strip() for p in parts):
        label = _identifier(part)
        if label and re.match(r"\s*:(?!=)", part[len(label):]):
            projections.append(_canonical(label))  # `part : Parent`: its own name
            continue
        while part.startswith("(") and part.endswith(")"):
            part = part[1:-1].strip()
        head = _identifier(part.lstrip("@"))
        last_part = head.split(".")[-1] if head else ""
        if not head or "«" in head or not last_part[:1].isupper():  # a term (`id Parent`), or a name it cannot spell
            projections.append(None)
        else:
            projections.append("to" + last_part)  # if the name is no alias for another structure: see `?toproj:`
    return projections


# Declarations that Lean adds for every inductive type (structures and classes included), and for
# each of its constructors. A few apply only to some types; reporting them for all is conservative.
_AUXILIARY = ("rec", "recOn", "casesOn", "noConfusionType", "noConfusion", "below", "brecOn", "ctorIdx",
              "ctorIdx._impl")  # the last two as Lean v4.36 makes them (see scripts/check_axioms.lean)
_CONSTRUCTOR_AUXILIARY = ("inj", "injEq", "sizeOf_spec")


def _derived(classes: str, type_name: str) -> list[str]:
    """The instances that `deriving <classes>` generates for the type `type_name` (qualified): Lean
    names them `inst<Class><Type>`, in the type's namespace."""
    namespace, last = _split_last(type_name)
    found = []
    for part in classes.split(","):
        part = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)*", "", part)  # `deriving @[expose] C`
        words = part.split()
        if words and _identifier(words[0]):
            name = f"inst{words[0].split('.')[-1]}{last}"
            found.append(f"{namespace}.{name}" if namespace else name)
        elif words:  # an item that it cannot read
            found.append(f"?gen:deriving:{type_name}")
    return found


def _parts(name: str) -> list[str]:
    """The components of a name, quoted ones whole: `A.«b.c»` gives A and «b.c»."""
    return re.findall(r"«[^»]*»|[^.«»]+", name) or [name]


def _constructors(text: str) -> list[str]:
    """The constructors that `| name ...` alternatives in `text` declare (`| @[simp] a`, `| protected a`)."""
    found = []
    for part in text.split("|")[1:]:
        part = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected)\s+)?", "", part)
        word = part.split()[0] if part.split() else ""
        if _identifier(word):
            found.append(word)
    return found


def declarations(text: str) -> list[tuple[str, int]]:
    """(qualified name, line) of each public named declaration, read line by line.

    A heuristic, not a parser. It follows `namespace`, `section`, `mutual` and `end`, and puts the
    enclosing namespaces before a name (`_root_.` drops them). `alias ⟨mp, mpr⟩` declares both names.
    In a file that starts with `module`, a declaration is private unless it is `public` or in a
    `public section` (or a `public namespace` or `mutual`). Modifiers alone on a line apply to the next one, and attributes may span lines.
    Generated names come from `_generated`, and from the indented lines under a structure, class or
    inductive: its fields, its constructor (`mk` unless it names one), the `toParent` projection of
    each structure it extends, and its constructors, with the declarations that Lean adds for every
    inductive type and constructor (`_AUXILIARY`). A structure's header runs to `where`; a line
    indented more than its first field continues the field above. A field line that it cannot read
    yields `?gen:structure:<name>`. `deriving C` after a type, and `deriving instance C for T`, add
    the instances that they generate. Each `?gen:` marker ends with `#` and a fingerprint of its
    attributes and its declaration's text. `initialize x : T` declares x, and a syntax command declares
    its `(name := x)`, or else yields `?gen:syntax:...`. A declaration may follow scoped commands on its line
    (`open X in`, `attribute [local instance] y in`); otherwise it misses declarations whose keyword
    does not start a line."""
    found, stack = [], []
    lines = strip_comments(text).split("\n")
    literal = strip_comments(text, keep_strings=True).split("\n")  # Lean names parsers after their literals
    module = next((line.split()[0] for line in lines if line.strip()), "") == "module"
    depth, carried, pending, attributes = 0, set(), None, ""
    marker_attributes: dict[tuple[str, int], str] = {}  # the attributes above each `?gen:` marker
    body: dict | None = None  # the structure, class or inductive whose indented lines come next
    last_type: str | None = None  # the last such type, which a `deriving` line after it extends
    last_local = False  # whether that type is module-local: what its clause makes is then possible only
    previous_code, expects_command, last = [""] * (len(lines) + 2), [False] * (len(lines) + 2), ""
    for index, text_line in enumerate(lines, 1):  # once per file, not once per line
        previous_code[index] = last
        expects_command[index] = bool(re.match(r"(?:open|set_option|attribute|#[\w!?]+|variable|include|omit|universe)\b", last)
                                      and re.search(r"\bin\s*$", last))  # `open Nat in` ends: a command follows
        if text_line.strip():
            last = text_line

    def left_open(number: int) -> bool:  # the line before goes on into this one
        return bool(_OPEN_END.search(previous_code[number])) and not expects_command[number]

    def open_clause(classes: str, number: int) -> None:
        """Classes of a `deriving` clause attached to the type in `body`; it goes on over the next
        lines while it has no class yet or ends with a comma."""
        derived = _derived(classes, body["name"])  # a local type's instances may still be public: possible names
        found.extend((f"?maybe:{name}" if body.get("local") and not name.startswith("?") else name, number)
                     for name in derived)
        body["deriving"] = not classes.strip() or classes.strip().endswith(",")
        body["deriving_line"] = number

    def constructor(type_name: str, name: str, number: int) -> None:
        found.append((f"{type_name}.{name}", number))
        found.extend((f"{type_name}.{name}.{aux}", number) for aux in _CONSTRUCTOR_AUXILIARY)

    def close() -> None:
        nonlocal body
        if body and body.get("deriving"):  # a clause whose classes never came: they cannot be read
            found.append((f"?gen:deriving:{body['name']}", body["deriving_line"]))
        if body and body["kind"] == "structure":
            if body["header"] is not None:  # no `where`: no fields, but the parents count
                end_header(body["header"], body["line"])
            if not body["constructor"]:
                if body.get("local"):
                    found.append((f"?local:{body['name']}.mk", body["line"]))
                else:
                    constructor(body["name"], "mk", body["line"])
        body = None

    def end_header(header: str, number: int) -> None:
        local = "?local:" if body.get("local") else ""
        parents = _parents(header)
        if any(re.match(r"to[A-Z]", p or "") for p in parents):  # a parent may be an alias: `toParent` for `Alias`
            found.append((f"?toproj:{body['name']}", number))
        for projection in parents:
            if projection is None:
                found.append((f"?gen:structure:{body['name']}", number))
                continue
            if not local:
                found.append((f"{body['name']}.{projection}", number))
            found.append((f"?local:{body['name']}.{projection}", number))  # its label: no field may take it
        body["header"] = None

    def read_field(text: str, number: int, indent: int) -> None:
        if body["field_indent"] is None or indent < body["field_indent"]:
            body["field_indent"] = indent
        elif indent > body["field_indent"]:
            return  # it continues the field above
        text = text.strip()
        if not text:
            return
        named = _CONSTRUCTOR.match(text)
        if named and _identifier(named.group(1)):
            body["constructor"] = True
            if body.get("local"):
                found.append((f"?local:{body['name']}.{named.group(1)}", number))
            else:
                constructor(body["name"], named.group(1), number)
            text = text[named.end():].strip()
            if not text:
                return
        names = _field_names(text)
        if names is None:
            found.append((f"?gen:structure:{body['name']}", number))
        else:  # a private field, or any field of a module-local structure, clashes only in its file
            for name in names:
                label = name[len("?local:"):] if name.startswith("?local:") else name
                if not name.startswith("?local:") and not body.get("local"):
                    found.append((f"{body['name']}.{label}", number))  # its public projection
                found.append((f"?local:{body['name']}.{label}", number))  # its label: one per structure, any visibility

    def read_body(line: str, number: int) -> None:
        stripped = line.strip()
        if not stripped:
            return
        if body.get("deriving"):  # the classes of a `deriving` clause go on
            open_clause(stripped, number)
            return
        deriving = re.search(r"\bderiving\b(.*)", stripped)
        if deriving and (body["header"] is None or body["kind"] == "inductive" or stripped.startswith("deriving")):
            open_clause(deriving.group(1), number)
            stripped = stripped[:deriving.start()].strip()
            if not stripped:
                return
        if body["kind"] == "inductive":
            if stripped.startswith("|"):
                body["ctors"] = body.get("ctors", 0) + 1
                for c in _constructors(stripped):
                    if body.get("local"):
                        found.append((f"?local:{body['name']}.{c}", number))
                    else:
                        constructor(body["name"], c, number)
            return
        if body["header"] is not None:  # binders and `extends` until `where`
            where = _WHERE.search(stripped)
            if not where:
                body["header"] += " " + stripped
                return
            end_header(body["header"] + " " + stripped[:where.start()], number)
            stripped = stripped[where.end():]
            if not stripped.strip():
                return
        read_field(stripped, number, len(line) - len(line.lstrip()))

    def default() -> bool:
        return stack[-1][2] if stack else not module

    def name_command(keyword: str, modifiers: set, after: str, number: int) -> None:
        """The names that an initializer or a syntax command declares."""
        if keyword in ("macro_rules", "elab_rules") or (keyword in ("macro", "elab") and re.search(r":\s*command\b", after)):
            # What a command macro or elaborator declares appears where it is used, in files that need not
            # change: a change to one (its fingerprint) is a hand check.
            prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
            found.append((f"?gen:command:{prefix + '.' if prefix else ''}{keyword}", number))
        if keyword == "declare_syntax_cat":  # public, in Lean.Parser.Category, whatever the scope
            category = _SCOPE_NAME.match(after)  # quote-aware: `«two words»`
            found.append((f"Lean.Parser.Category.{category.group(1)}" if category else
                          "?gen:syntax:Lean.Parser.Category.declare_syntax_cat", number))
            return
        if keyword in _SYNTAX_COMMANDS:  # Lean exports a syntax declaration unless it is local
            if "private" in modifiers or "local" in modifiers:
                return
        elif "private" in modifiers or not ("public" in modifiers or default()):
            return
        prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
        name = None
        if keyword in _INITIALIZERS:
            head = _SCOPE_NAME.match(after)  # `initialize x : T`, x quote-aware
            if head and after[head.end():].lstrip().startswith(":"):
                name = head.group(1)
        else:
            explicit = re.search(r"\(\s*name\s*:=", after)
            if explicit:  # `(name := x)`, x quote-aware; one it cannot read is not guessed at
                inner = _SCOPE_NAME.match(after, explicit.end())
                if not inner or not after[inner.end():].lstrip().startswith(")"):
                    found.append((f"?gen:syntax:{prefix + '.' if prefix else ''}{keyword}", number))
                    return
                name = inner.group(1)
        if name:
            qualified = name[len("_root_."):] if name.startswith("_root_.") else f"{prefix}.{name}" if prefix else name
            found.append((qualified, number))
        elif keyword in _SYNTAX_COMMANDS and keyword not in ("macro_rules", "elab_rules") \
                and "local" not in modifiers:  # a name made up from the syntax
            line = literal[number - 1]
            command = re.search(rf"\b{keyword}\b", line)
            generated = _parser_name(keyword, line[command.end():]) if command else None
            if generated:  # Lean takes the base, or base_1, base_2, ... if it is taken: which one is not known
                component = _component(generated)  # one component, whatever its characters
                found.append((f"?parser:{f'{prefix}.{component}' if prefix else component}", number))
            else:
                found.append((f"?gen:syntax:{prefix + '.' if prefix else ''}{keyword}", number))

    def record(keyword: str, modifiers: set, rest: str, number: int, attributes: str) -> None:
        nonlocal body, last_type, last_local
        if re.search(r"\b(?:command_elab|macro)\b", attributes or ""):  # `@[command_elab k] def`: as an elaborator
            prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
            marker = f"?gen:command:{prefix + '.' if prefix else ''}command_elab"
            found.append((marker, number))
            marker_attributes[(marker, number)] = " ".join(attributes.split())  # which syntax it serves counts
        if keyword == "attribute":  # an attribute list that went on over several lines
            attribute_command(rest, number)
            return
        if keyword == "open":  # a rename list that went on over several lines
            number_now[0] = number
            open_namespaces(rest)
            return
        if keyword == "namespace":  # a header whose name came on a later line
            scope = _SCOPE_NAME.match(rest)
            if scope:
                visible = True if "public" in modifiers else False if "private" in modifiers else default()
                stack.extend(("namespace", part, visible) for part in _parts(_canonical(scope.group(1))))
            return
        if keyword in _INITIALIZERS | _SYNTAX_COMMANDS:
            name_command(keyword, modifiers, rest, number)
            return
        prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
        local = "private" in modifiers or not ("public" in modifiers or default())
        if keyword == "deriving" and local:  # `private deriving instance C for T`: what it makes may be public
            before = len(found)
            derive(rest, number)
            found[before:] = [(n if n.startswith("?") else f"?maybe:{n}", line) for n, line in found[before:]]
            return
        if local or keyword.endswith("_wanted"):
            # Module-local (Batteries makes every `*_wanted` placeholder private): two such names clash only
            # in one file, so they are kept apart from the public names, as `?local:`.
            local_names = []
            for n in _declared_names(keyword, re.sub(r"^\s*inductive\b", "", rest)):
                n = n[len("_root_."):] if n.startswith("_root_.") else f"{prefix}.{n}" if prefix else n
                found.append((f"?local:{n}", number))
                local_names.append(n)
            inductive = keyword == "inductive" or (keyword == "class" and re.match(r"\s*inductive\b", rest))
            if keyword in ("structure", "class", "inductive") and local_names:
                last_type, last_local = local_names[0], True
                declared = lines[number - 1]  # its members are module-local too: read them as such
                indent = len(declared) - len(declared.lstrip())
                deriving = re.search(r"\bderiving\b(.*)", rest)
                head = rest[:deriving.start()] if deriving else rest
                where = _WHERE.search(head)
                body = {"kind": "inductive" if inductive else "structure", "name": local_names[0], "line": number,
                        "constructor": False, "indent": indent, "header": None if where or inductive else head,
                        "field_indent": None, "local": True}
                if inductive:
                    for c in _constructors(head):
                        found.append((f"?local:{local_names[0]}.{c}", number))
                elif where:
                    end_header(head[:where.start()], number)  # its parents' projections, as module-local names
                    if head[where.end():].strip():
                        read_field(head[where.end():], number, indent + 1)
                if deriving:  # `private inductive T | a | b deriving DecidableEq`: on its own line
                    open_clause(deriving.group(1), number)
            return
        if keyword == "deriving":
            derive(rest, number)
            return
        inductive_class = keyword == "class" and bool(re.match(r"inductive\b", rest))
        if inductive_class:
            rest = rest[len("inductive"):]

        def qualify(name: str) -> str:
            return name[len("_root_."):] if name.startswith("_root_.") else f"{prefix}.{name}" if prefix else name

        names = [qualify(name) for name in _declared_names(keyword, rest)]
        generated = _generated(keyword, names, rest, attributes, qualify)
        found.extend((name, number) for name in names + generated)
        if keyword in ("def", "abbrev", "instance") and names and not names[0].startswith("?") \
                and not any(n.startswith("?inst:") for n in generated):
            found.append((f"?eqns:{names[0]}", number))  # the equation and induction names Lean reserves for it
        nonlocal helper
        where = _WHERE.search(rest)
        if keyword in _HELPER_PARENTS and names and not names[0].startswith("?") \
                and not any(n.startswith("?inst:") for n in generated) \
                and not (where and ":=" not in rest[:where.start()]):  # `where` after a signature: fields
            # Its `where` helpers and `let rec` functions are declarations under its name.
            helper = {"name": names[0], "assigned": ":=" in rest or bool(re.search(r"(^|\s)\|", rest)),
                      "where": None, "indent": None, "outer": None, "last": None}
            for rec in _let_recs(rest):  # on its own line too
                found.extend([(f"{names[0]}.{rec}", number), (f"?eqns:{names[0]}.{rec}", number)] if rec
                             else [(f"?gen:helper:{names[0]}", number)])
            if where:  # `def f := go where` (`where` after its body): the helpers start here
                declared = lines[number - 1]
                helper["where"] = len(declared) - len(declared.lstrip())
                if rest[where.end():].strip():
                    add_helper(rest[where.end():].strip(), number)
        for name in generated:
            if name.startswith("?gen:"):
                marker_attributes[(name, number)] = " ".join(attributes.split())
        if names and keyword in ("structure", "class", "inductive"):
            last_type, last_local = names[0], False
            found.extend((f"{names[0]}.{aux}", number) for aux in _AUXILIARY)
            if re.search(r"\bto_additive\b", attributes):  # its copy's members cannot be predicted
                found.append((f"?gen:to_additive:{names[0]}", number))
                marker_attributes[(f"?gen:to_additive:{names[0]}", number)] = " ".join(attributes.split())
            inductive = keyword == "inductive" or inductive_class
            declared = lines[number - 1]
            indent = len(declared) - len(declared.lstrip())
            body = {"kind": "inductive" if inductive else "structure", "name": names[0], "line": number,
                    "constructor": False, "indent": indent, "header": rest, "field_indent": None}
            if inductive:
                deriving = re.search(r"\bderiving\b(.*)", rest)
                for c in _constructors(rest[:deriving.start()] if deriving else rest):
                    constructor(names[0], c, number)
                if deriving:
                    open_clause(deriving.group(1), number)
            else:
                where = _WHERE.search(rest)
                if where:
                    end_header(rest[:where.start()], number)
                    if rest[where.end():].strip():  # fields on the declaration's line
                        read_field(rest[where.end():], number, indent + 1)

    def unfinished(keyword: str, text: str) -> bool:
        """A keyword that ends its line, a paired alias whose names go on over the next lines, or a
        `deriving` command whose classes or targets do."""
        text = text.strip()
        if keyword == "attribute":
            return not text or _open_list(text)
        if keyword == "open":
            return bool(re.search(r"(?:\brenaming|,|→|->)$", text))
        if keyword == "namespace":
            return not text  # its name may be on the next line
        if keyword in _INITIALIZERS:
            return not text  # `initialize` alone on its line: its name comes next
        if keyword in _SYNTAX_COMMANDS:
            return False
        if keyword == "deriving":
            if not text or text.endswith(","):
                return True
            command = re.match(r"(?:noncomputable\s+)?instance\b", text)
            return bool(command) and not re.search(r"\bfor\b\s*\S", text)
        return not text or (keyword == "alias" and text.startswith("⟨") and "⟩" not in text)

    def derive(text: str, number: int) -> None:
        """The instances that a `deriving` command generates."""
        prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
        command = re.match(r"\s*(?:noncomputable\s+)?instance\b(.*?)\bfor\b(.*)", text, re.S)
        if command:
            targets = [t.split()[0] if t.split() else "" for t in command.group(2).split(",")]
            classes, readable = command.group(1), all(_identifier(t) for t in targets) and targets
            for target in targets if readable else []:
                last = target.split(".")[-1]
                found.extend((name, number) for name in _derived(classes, f"{prefix}.{last}" if prefix else last))
        elif re.match(r"\s*(?:noncomputable\s+)?instance\b", text) or not last_type:
            readable = False
        else:
            classes = text
            readable = any(c.split() for c in classes.split(","))
            found.extend((f"?maybe:{name}" if last_local and not name.startswith("?") else name, number)
                         for name in _derived(text, last_type))
        if not readable:
            found.append((f"?gen:deriving:{prefix + '.' if prefix else ''}instance", number))

    restore = None  # the scopes as they were before a `scoped[NS]` command
    command_level = True  # whether an indented line here can only be a command, not the last one's continuation
    command_indent = 0  # the indentation of the last command: a line at or left of it is not its continuation
    opened: list[str] = []  # every namespace the file opens, wherever: where `attribute` may find its targets
    renamed: dict[str, list[str]] = {}  # `open N renaming a → b`: what b may stand for
    number_now = [0]  # the line being read, for markers made while reading an `open`
    attribute_open = None  # the attributes of an `attribute` command whose targets may go on over the next lines

    def chain_of() -> list[str]:
        """The enclosing namespaces, innermost first and the root last: `namespace A.B` gives A.B, A, ''."""
        prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
        parts = re.findall(r"«[^»]*»|[^.«»]+", prefix)
        return [".".join(parts[:i]) for i in range(len(parts), -1, -1)]

    def open_namespaces(text: str) -> None:
        """`open Inner` inside `namespace Outer` may open Outer.Inner or Inner: every reading counts.
        `open N renaming a → b` makes `b` stand for N.a."""
        space = _identifier(text.strip())
        after_space = text.strip()[len(space):] if space else ""

        def under(name: str) -> list[str]:  # `_root_.N` is N wherever it is opened
            return [_canonical(name[len("_root_."):])] if name.startswith("_root_.") else \
                [_canonical(f"{c}.{name}" if c else name) for c in chain_of()]
        if space and re.match(r"\s+renaming\b", after_space):
            rest = re.sub(r"^\s+renaming\s*", "", after_space)
            while rest.strip():
                original = _identifier(rest.strip())
                rest = rest.strip()[len(original):] if original else rest
                arrow = re.match(r"\s*(?:→|->)\s*", rest)
                local = _identifier(rest[arrow.end():]) if arrow and original else None
                if not local:  # a rename it cannot read: an attribute on it cannot be resolved
                    found.append((f"?gen:open:{chain_of()[0] or 'root'}.{space}", number_now[0]))
                    return
                renamed.setdefault(_canonical(local), []).extend(under(f"{space}.{original}"))
                rest = re.sub(r"^\s*,?", "", rest[arrow.end() + len(local):])
            text = space
        rest = text
        while rest.strip():  # quote-aware: `open «Two Words» Other`
            rest = rest.strip()
            if rest[:1] in "()":
                rest = rest[1:]
                continue
            name = _identifier(rest)
            if not name:
                rest = rest.split(None, 1)[1] if len(rest.split(None, 1)) > 1 else ""
                continue
            rest = rest[len(name):]
            if name not in ("scoped", "hiding", "renaming", "in"):
                opened.extend(under(name))

    def attribute_targets(attrs: str, targets: str, number: int) -> None:
        """The names `attrs` generate for each target in `targets`. A relative target resolves in the
        innermost enclosing namespace that has it, an opened one, or the root, which preflight cannot
        tell apart: with more than one candidate, the names are only possible ones (`?maybe:`)."""
        prefix = chain_of()[0]

        def qualify(name: str) -> str:
            return name[len("_root_."):] if name.startswith("_root_.") else f"{prefix}.{name}" if prefix else name
        rest = targets.strip()
        while rest:
            target = _identifier(rest)
            if not target:  # a token it cannot read as a name: it may still be a target
                found.append((f"?gen:attribute:{prefix + '.' if prefix else ''}{rest.split()[0]}", number))
                return
            rest = rest[len(target):].lstrip()
            aliases = [original + _canonical(target)[len(local):] for local, originals in renamed.items()
                       if _canonical(target) == local or _canonical(target).startswith(local + ".")
                       for original in originals]
            candidates = [target[len("_root_."):]] if target.startswith("_root_.") else \
                list(dict.fromkeys([f"{c}.{target}" if c else target for c in chain_of() + opened] + aliases))
            declared = {_canonical(n) for n, _ in found if not n.startswith("?")}
            if candidates and _canonical(candidates[0]) in declared:  # the nearest one exists: Lean takes it
                candidates = candidates[:1]
            generated = dict.fromkeys(name for candidate in candidates
                                      for name in _generated("structure", [candidate], "", attrs, qualify))
            found.extend((name if len(candidates) == 1 or name.startswith("?") else f"?maybe:{name}", number)
                         for name in generated)

    def attribute_command(after: str, number: int) -> bool:
        """`attribute [reassoc] foo bar`: True if its targets may go on over the next lines."""
        listed = _attribute_list(after)
        if not listed:
            return False
        nonlocal attribute_open
        wrapper = re.search(r"\bin\s*$", listed[1])  # `attribute [local instance] f in`: a command follows
        attribute_targets(listed[0], listed[1][:wrapper.start()] if wrapper else listed[1], number)
        attribute_open = None if wrapper else listed[0]
        return not wrapper
    helper = None  # the declaration whose `where` helpers and `let rec` functions the next lines may declare

    def add_helper(text: str, number: int) -> None:
        """A helper declared by `text`, a line of a `where` block, with its own `let rec` functions; a
        `where` after its body opens a block of its own helpers."""
        nonlocal helper
        if text.startswith("|") or re.match(r"(?:termination_by|decreasing_by|deriving|where)\b", text):
            return  # an alternative, or no helper
        name = _identifier(text)  # quote-aware: `«two words»`
        if not name:
            found.append((f"?gen:helper:{helper['name']}", number))  # a helper it cannot read
            return
        found.append((f"{helper['name']}.{name}", number))
        found.append((f"?eqns:{helper['name']}.{name}", number))  # a helper is a definition
        helper["last"] = name
        for rec in _let_recs(text):
            owner = f"{helper['name']}.{name}"
            found.extend([(f"{owner}.{rec}", number), (f"?eqns:{owner}.{rec}", number)] if rec
                         else [(f"?gen:helper:{owner}", number)])
        tail = _WHERE.search(text)
        if tail and ":=" in text[:tail.start()]:  # `g := h where`: g's helpers follow
            nest(len(lines[number - 1]) - len(lines[number - 1].lstrip()), text[tail.end():].strip(), number)

    def nest(indent: int, rest_of_line: str, number: int) -> None:
        """Open the `where` block of the last helper."""
        nonlocal helper
        helper = {"name": f"{helper['name']}.{helper['last']}", "assigned": True, "where": indent, "indent": None,
                  "outer": helper, "last": None}
        if rest_of_line:
            add_helper(rest_of_line, number)
    for number, line in enumerate(lines, 1):
        if restore is not None and not pending and not carried:  # `scoped[NS]` alone on a line holds for the next command
            stack[:], restore = restore, None
        if body is not None and not pending:
            indent = len(line) - len(line.lstrip())
            if not line.strip() or indent > body["indent"] or \
                    (body["kind"] == "inductive" and line.lstrip().startswith("|") and indent >= body["indent"]) or \
                    (re.match(r"where\b", line.strip()) and indent == body["indent"]  # `structure S (α : Type)` then `where`
                     and (body["header"] is not None or (body["kind"] == "inductive" and not body.get("ctors")))):
                read_body(line, number)
                continue
            close()
        rest, depth = _skip_attributes(line, depth)
        attributes += " " + line[:len(line) - len(rest)]
        if not rest.strip():
            continue
        if pending and pending[0] == "deriving" and not line[:1].isspace():
            keyword, modifiers, at, text, held = pending
            record(keyword, modifiers, text, at, held)  # a new command starts: the clause ends with what it has
            pending = None
        if pending:  # the declaration's names start on, or go on over, this line
            keyword, modifiers, at, text, held = pending
            text = f"{text} {rest}"
            pending = (keyword, modifiers, at, text, held) if unfinished(keyword, text) else None
            if not pending:
                record(keyword, modifiers, text, at, held)
            continue
        if attribute_open is not None:  # an `attribute` command's targets may go on over deeper lines
            if line[:1].isspace() and len(line) - len(line.lstrip()) > command_indent and \
                    not (_WORD.match(rest) and _WORD.match(rest).group(1) in _COMMANDS):
                attribute_targets(attribute_open, rest, number)
                continue
            attribute_open = None
        if helper is not None:  # the lines after a definition: its helpers
            indent, text = len(line) - len(line.lstrip()), rest.strip()
            while helper is not None and helper["where"] is not None and indent <= helper["where"]:
                helper = helper["outer"]  # that block has ended: back to the one around it, if any
        if helper is not None and helper["where"] is not None:  # inside a `where` block
            helper["indent"] = helper["indent"] or indent
            if re.match(r"where\b", text):  # the last helper's own helpers
                if helper["last"]:
                    nest(indent, text[len("where"):].strip(), number)
            elif indent == helper["indent"]:
                add_helper(text, number)
            elif helper["last"]:  # inside a helper's body
                for rec in _let_recs(text):
                    owner = f"{helper['name']}.{helper['last']}"
                    found.extend([(f"{owner}.{rec}", number), (f"?eqns:{owner}.{rec}", number)] if rec
                                 else [(f"?gen:helper:{owner}", number)])
            continue
        if helper is not None:
            if re.match(r"where\b", text):
                if helper["assigned"]:  # after its body: helper declarations follow
                    helper["where"] = indent
                    if text[len("where"):].strip():
                        add_helper(text[len("where"):].strip(), number)
                    continue
                helper = None  # after its signature: a structure instance's fields
                continue
            else:
                helper["assigned"] = helper["assigned"] or ":=" in text or text.startswith("|")
                for rec in _let_recs(text):
                    found.extend([(f"{helper['name']}.{rec}", number), (f"?eqns:{helper['name']}.{rec}", number)] if rec
                                 else [(f"?gen:helper:{helper['name']}", number)])
        wrapper = _IN_PREFIX.match(rest)
        if wrapper:  # `open MyNs in attribute [reassoc] probe`: MyNs is open for that command
            for opening in re.finditer(r"\bopen\s+(.*?)\s+in\b", wrapper.group(0)):
                open_namespaces(opening.group(1))
        rest = _IN_PREFIX.sub("", rest)
        probe = rest  # the first word after any modifiers: `local notation ... in` is no declaration
        while (word := _WORD.match(probe)) and word.group(1) in _MODIFIERS:
            probe = _skip_attributes(probe[word.end():])[0]
        first = _WORD.match(probe)
        if first and first.group(1) not in _DECLARATIONS | {"namespace", "section", "end", "mutual", "deriving"}:
            scoped = _SCOPED_IN.sub("", rest, count=1)
            if scoped != rest:  # a declaration after a scoped command on this line
                rest, depth = _skip_attributes(scoped, depth)
                attributes += " " + scoped[:len(scoped) - len(rest)]
        modifiers, carried = carried, set()
        while True:
            word = _WORD.match(rest)
            if not word or word.group(1) not in _MODIFIERS:
                break
            modifiers = modifiers | {word.group(1)}
            tail = rest[word.end():]
            selector = _SELECTOR.match(tail) if word.group(1) == "scoped" and not word.group(0).endswith(" ") else None
            if selector:  # `scoped[NS] command`: the command is in namespace NS, as Mathlib's weak namespace puts it
                restore = stack[:]
                stack[:] = [e for e in stack if e[0] != "namespace"] + [("namespace", _canonical(selector.group(1)), True)]
                tail = tail[selector.end():]
            rest, depth = _skip_attributes(tail, depth)
            attributes += " " + tail[:len(tail) - len(rest)]
        word = _WORD.match(rest)
        if word and re.match(r"[\w!?«]", rest[word.end(1):word.end(1) + 1]):
            word = None  # `emit2 dup`, `EmitDef! dup`: not a word it knows, read below as a command it does not
        if not word:
            if not rest.strip():
                carried = modifiers
            indent = len(line) - len(line.lstrip())
            token = re.match(r"(«[^»]*»|[^\W\d][\w.'!?]*)", rest)  # a letter of any script: `λemit`, `Σcmd`
            if not token and expects_command[number] and rest.strip() and not rest.startswith("#"):
                token = re.match(r"(\S+)", rest)  # `open Nat in` then `§ dup`: whatever comes is a command
            if token and not rest.startswith("#") and body is None \
                    and (not line[:1].isspace() or command_level or indent <= command_indent or expects_command[number]) \
                    and not _CONTINUATION.match(rest[token.end():]) \
                    and not left_open(number):
                prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
                name = re.sub(r"[^\w.]", "", token.group(1)) or "command"
                found.append((f"?gen:command:{prefix + '.' if prefix else ''}{name}", number))  # it may declare anything
                helper, command_level, command_indent = None, False, indent
                continue
            hashed = re.match(r"#[A-Za-z_][\w.!?]*", rest)  # `#emit_def dup`: a command macro may start so
            indent = len(line) - len(line.lstrip())
            if hashed and hashed.group(0) not in _HARMLESS_HASH and body is None \
                    and (not line[:1].isspace() or command_level or indent <= command_indent):
                prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
                found.append((f"?gen:command:{prefix + '.' if prefix else ''}{hashed.group(0)[1:]}", number))  # `#` aside
                helper, command_level, command_indent = None, False, indent
            continue
        held, attributes = attributes, ""  # the attributes belong to this command
        keyword, after = word.group(1), rest[word.end():]
        indent = len(line) - len(line.lstrip())
        boundary = not line[:1].isspace() or command_level or indent <= command_indent or expects_command[number]
        if keyword in _COMMANDS:
            if boundary:  # deeper in a proof, `module` or `open` is a tactic: the command goes on
                helper = None  # another command: the definition's lines have ended
                command_level = keyword in ("namespace", "section", "end")  # the others may go on over indented lines
                command_indent = indent
        elif boundary and body is None \
                and keyword not in _HARMLESS | _MODIFIERS | _TERM_KEYWORDS \
                and not _CONTINUATION.match(after) \
                and not left_open(number):
            # (a line after one left open, `theorem t : True :=` then `trivial`, continues it)
            # attributes, modifiers and `... in` stripped: `@[attr] public my_macro dup`, indented or not
            prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
            found.append((f"?gen:command:{prefix + '.' if prefix else ''}{keyword}", number))  # it may declare anything
            helper, command_level, command_indent = None, False, indent  # it is not read, whatever it is
        scope = _SCOPE_NAME.match(after)  # the whole name: `namespace «A B»`; `namespace «N»` is N, as `end N` says
        argument = _canonical(scope.group(1)) if scope else None
        visible = True if "public" in modifiers else False if "private" in modifiers else default()
        if keyword == "namespace":
            if argument:  # `namespace A.B` opens A, then B: `end B` closes B alone
                stack.extend(("namespace", part, visible) for part in _parts(argument))
            else:
                pending = (keyword, modifiers, number, after, held)
        elif keyword == "section":
            stack.append(("section", argument, visible))
        elif keyword == "mutual":
            stack.append(("mutual", None, visible))
        elif keyword == "attribute":
            if _open_list(after) or not after.strip():  # the attribute list goes on over the next lines
                pending = (keyword, modifiers, number, after, held)
            else:
                attribute_command(after, number)
        elif keyword == "open":
            number_now[0] = number
            if unfinished(keyword, after):  # `open N renaming` with its list on the next lines
                pending = (keyword, modifiers, number, after, held)
            else:
                open_namespaces(after)
        elif keyword in _INITIALIZERS | _SYNTAX_COMMANDS:
            if unfinished(keyword, after):
                pending = (keyword, modifiers, number, after, held)
            else:
                name_command(keyword, modifiers, after, number)
        elif keyword == "deriving":
            if unfinished(keyword, after):
                pending = (keyword, modifiers, number, after, held)
            else:
                record(keyword, modifiers, after, number, held)
        elif keyword == "end":
            if argument is None:
                if stack:
                    stack.pop()
            else:
                parts = _parts(argument)
                if len(stack) >= len(parts) and [frame[1] for frame in stack[-len(parts):]] == parts:
                    del stack[-len(parts):]  # `end A.B` closes B, then A
                else:
                    for index in range(len(stack) - 1, -1, -1):
                        if stack[index][1] == argument:
                            del stack[index:]
                            break
        elif keyword in _DECLARATIONS:
            if unfinished(keyword, after):
                pending = (keyword, modifiers, number, after, held)
            else:
                record(keyword, modifiers, after, number, held)
        own = re.sub(r"^\s*(?:noncomputable\s+)?(?:instance|inductive)\b", "", after) if keyword in ("deriving", "class") \
            else after
        own = re.sub(r"\[[^\[\]]*\]", " ", own)  # attribute lists: `attribute [local instance 5] f`
        again = _AGAIN.search(own) if keyword in _COMMANDS else None  # `deriving instance`, `class inductive` aside
        if again:  # another command on the same line: not read, so the check is incomplete
            prefix = ".".join(n for kind, n, _ in stack if kind == "namespace" and n)
            found.append((f"?gen:line:{prefix + '.' if prefix else ''}{again.group(1) or again.group(2)}", number))
    close()
    if pending and pending[0] == "attribute":  # still open at the end: its targets cannot be read
        found.append((f"?gen:attribute:{'.'.join(n for kind, n, _ in stack if kind == 'namespace' and n) or 'file'}",
                      pending[2]))
    # A marker for names it cannot predict carries a fingerprint of its attributes and its declaration's
    # text, comments and spacing aside, so that an edit to either (say, to the projections `@[simps]`
    # lists) reads as a new marker.
    def fingerprint(name: str, line: int) -> str:
        """Over its attributes and its own lines: its first line, then the lines indented deeper."""
        indent = len(lines[line - 1]) - len(lines[line - 1].lstrip())
        end = line
        while end < len(lines) and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > indent
                                    or (lines[end].lstrip().startswith("|")
                                        and len(lines[end]) - len(lines[end].lstrip()) == indent)):  # `| alt` of a rule
            end += 1
        text = marker_attributes.get((name, line), "") + "\n" + " ".join(" ".join(literal[line - 1:end]).split())
        return hashlib.sha1(text.encode()).hexdigest()[:12]

    return [(f"{name}#{fingerprint(name, line)}" if name.startswith("?gen:") else
             f"?local:{_canonical(name[len('?local:'):])}" if name.startswith("?local:") else
             f"?maybe:{_canonical(name[len('?maybe:'):])}" if name.startswith("?maybe:") else
             f"?eqns:{_canonical(name[len('?eqns:'):])}" if name.startswith("?eqns:") else
             f"?toproj:{_canonical(name[len('?toproj:'):])}" if name.startswith("?toproj:") else
             name if name.startswith("?") else _canonical(name), line) for name, line in found]


def placed_declarations(changes: list[tuple[str, str, str]], texts: dict[str, str],
                        parsed: dict | None = None) -> dict[str, list[tuple[str, int]]]:
    """Where the new side of each change declares a name more often than its old side did: a name
    added there, or moved there from another file. Every copy of such a name in that file is listed."""
    placed: dict[str, list[tuple[str, int]]] = {}
    if len(changes) > MAX_FILES_READ:
        raise Failure(f"{len(changes)} files to read, more than the {MAX_FILES_READ} that preflight reads")
    parsed = {} if parsed is None else parsed  # one parse per blob, however many paths have it

    def of(oid: str) -> list[tuple[str, int]]:
        if oid not in parsed:
            parsed[oid] = declarations(texts[oid])
        return parsed[oid]
    for old_oid, new_oid, path in changes:
        if new_oid == ZERO_OID:
            continue
        before = collections.Counter(name for name, _ in of(old_oid)) if old_oid != ZERO_OID \
            else collections.Counter()
        found = of(new_oid)
        after = collections.Counter(name for name, _ in found)
        for name, line in found:
            if after[name] > before[name]:
                placed.setdefault(name, []).append((path, line))
    return placed


# --------------------------------------------------------------------------------------------------
# Gathering facts


def is_library_lean(path: str) -> bool:
    return path.endswith(".lean") and path.split("/", 1)[0] in LIBRARIES


def head_changes(git: Git, main: str, heads: list[str]) -> dict[str, list[tuple[str, str, str]]]:
    """Each head's changes since its merge base with main. First it downloads, in one request, the
    blobs that the merges and the duplicate check read. Those are the libraries' Lean files, and
    every file that two heads change, or that one head and main change since the oldest merge base."""
    changes = {sha: git.diff_raw(git.merge_base(main, sha) or main, sha, ()) for sha in dict.fromkeys(heads)}
    touched: dict[str, int] = {}
    for diff in changes.values():
        for _, _, path in diff:
            touched[path] = touched.get(path, 0) + 1
    oldest = git.out("merge-base", "--octopus", main, *changes) if changes else main
    on_main = set(git.changed_files(oldest, main)) if oldest else set()
    shared = {path for path, count in touched.items() if count > 1 or path in on_main}
    oids = {oid for diff in changes.values() for old, new, path in diff
            if path in shared or is_library_lean(path) for oid in (old, new)}
    if shared:
        oids.update(git.root_oids(main, tuple(sorted(shared))).values())
    git.prefetch(oids)
    return changes


def _chain(git: Git, main: str, entries: list[dict], leave: frozenset = frozenset()) -> dict:
    """Merge the queued heads onto main in order, as the queue builds its merge groups, without the
    entries numbered in `leave`. An entry that conflicts with the merge of those ahead is left out."""
    tip, merged, skipped, tips, flags, pins = main, [], [], [], [], {}
    tip_pins = git.root_oids(main, PIN_FILES)
    for entry in entries:
        if entry["number"] in leave:
            continue
        record = {"number": entry["number"], "position": entry["position"]}
        attempt = git.merge_tree(tip, entry["head"])
        if not attempt["clean"]:
            flags.append(dict(record, clean=False, files=attempt["files"]))
            skipped.append((record, entry))
            continue
        tip = git.commit_tree(attempt["tree"], [tip, entry["head"]], f"Merge pull request #{entry['number']}")
        flags.append(dict(record, clean=True))
        merged.append(f"#{entry['number']}")
        tips.append((record, tip))
        after = git.root_oids(tip, PIN_FILES)
        if after != tip_pins:  # this merge changes the pins, whatever its own diff says
            pins[entry["number"]] = sorted(path for path in set(after) | set(tip_pins)
                                           if after.get(path) != tip_pins.get(path))
        tip_pins = after
    return {"tip": tip, "merged": merged, "skipped": skipped, "tips": tips, "entries": flags, "pins": pins}


def _admit(git: Git, main: str, entries: list[dict], entry: dict, limit: int = 3):
    """The entries ahead whose leaving keeps `entry` queued, and the queue without them; "removed"
    when the queue removes it whatever leaves; None when this search cannot tell.

    If `entry` merges with main, its blockers are found one at a time: each is the entry after which
    `entry`, which merged with main and the entries before it, no longer merges.

    If it conflicts with main, only an entry ahead that changes the conflicted files once merged
    onto main (renames included) or changes a .gitattributes, or that shares history with it that main
    does not have (any of their best merge bases is outside main), can let it merge. With none, it is removed. Otherwise, for each such entry that alone lets it merge, the
    other entries that make it conflict again on top of that one are its blockers; the queue without
    them must then keep it. Fixes that need two entries together are not searched: None."""
    ahead = [e for e in entries if e["position"] < entry["position"]]
    with_main = git.merge_tree(main, entry["head"])
    if not with_main["clean"]:
        conflicted, fixers = set(with_main["files"]), []
        for e in ahead:
            merged = git.merge_tree(main, e["head"])
            bases = git.run("merge-base", "--all", e["head"], entry["head"], check=False).stdout.split()
            paths = {path for _, _, path in git.diff_raw(main, merged["tree"], ())} if merged["clean"] else set()
            if not merged["clean"] or conflicted & paths or any(p.rsplit("/", 1)[-1] == ".gitattributes" for p in paths) \
                    or not bases or any(not git.is_ancestor(base, main) for base in bases):
                fixers.append(e)  # it may change how the entry merges (attributes too), or cannot be read
        if not fixers:
            return "removed"
        for fixer in fixers[:limit]:
            if not git.merge_tree(_chain(git, main, [fixer])["tip"], entry["head"])["clean"]:
                continue  # it does not let it merge on its own
            leave = frozenset(e["number"] for e in ahead if e is not fixer and not git.merge_tree(
                _chain(git, main, sorted([fixer, e], key=lambda x: x["position"]))["tip"], entry["head"])["clean"])
            chain = _chain(git, main, entries, leave)
            if len(leave) <= limit and f"#{entry['number']}" in chain["merged"]:
                return leave, chain
        return None
    leave: frozenset = frozenset()
    for _ in range(limit + 1):
        chain = _chain(git, main, entries, leave)
        if f"#{entry['number']}" in chain["merged"]:
            return leave, chain
        merged_before, blocker = True, None
        for ahead_entry, tip in chain["tips"]:
            if ahead_entry["position"] > entry["position"]:
                break
            clean = git.merge_tree(tip, entry["head"])["clean"]
            if merged_before and not clean:
                blocker = ahead_entry["number"]
                break
            merged_before = clean
        if blocker is None:
            return None
        leave = leave | {blocker}
    return None


def simulate(git: Git, main: str, entries: list[dict], head: str, changes: dict[str, list]) -> dict:
    """Merge main, every queued head in order, then `head`, as the queue builds merge groups.

    An entry that conflicts with the entries ahead of it is left out, as the queue removes it. But it
    stays if the entries it conflicts with (its blockers, found one at a time by `_admit`) leave
    first, and the entries behind it then merge on top of it. So `head` is also merged onto the queue
    without each union of the left-out entries' blocker sets (at most 31, with MAX_LEFT_OUT entries).
    A left-out entry that no explored queue keeps, or more than MAX_LEFT_OUT of them, cannot be
    checked. Every entry whose own changes touch
    the pins counts, merged or not."""
    # An entry changes the pins if its own diff does, if a simulated merge of it does, or, when it
    # merges nowhere, if its diff from any of its best merge bases with main does.
    pin_files: dict[int, set] = {e["number"]: {path for _, _, path in changes[e["head"]]} & set(PIN_FILES)
                                 for e in entries}
    result = {"main": git.merge_tree(main, head), "entries": [], "candidate": None, "pin_changes_ahead": []}
    queue = _chain(git, main, entries)
    result["entries"], result["tip"] = queue["entries"], queue["tip"]

    def note_pins(chain: dict) -> None:
        for number, paths in chain["pins"].items():
            pin_files[number] |= set(paths)

    def finish() -> dict:
        for record, entry in queue["skipped"]:
            for base in git.run("merge-base", "--all", main, entry["head"], check=False).stdout.split() or [main]:
                pin_files[entry["number"]] |= {path for _, _, path in git.diff_raw(base, entry["head"], PIN_FILES)}
        result["pin_changes_ahead"] = [dict(number=e["number"], position=e["position"],
                                            files=sorted(pin_files[e["number"]]))
                                       for e in entries if pin_files[e["number"]]]
        return result

    note_pins(queue)
    if not result["main"]["clean"]:
        return finish()
    merged = git.merge_tree(queue["tip"], head)
    candidate = dict(merged, conflicts_with=None, uncertain=[], alternatives={}, partial=None, unexplored=0)
    if not merged["clean"]:
        # Find the first entry it conflicts with, and keep the merge onto the entries ahead of that one.
        before = {"base": main, "tree": result["main"]["tree"], "entries": []}
        for record, partial in queue["tips"]:
            attempt = git.merge_tree(partial, head)
            if not attempt["clean"]:
                candidate["conflicts_with"] = dict(record, files=attempt["files"])
                break
            before = {"base": partial, "tree": attempt["tree"], "entries": before["entries"] + [f"#{record['number']}"]}
        candidate["partial"] = before
    result["candidate"] = candidate
    if len(queue["skipped"]) > MAX_LEFT_OUT:
        candidate["unexplored"] = len(queue["skipped"])
        return finish()
    blockers: dict[int, frozenset] = {}
    for record, entry in queue["skipped"]:
        admitted = _admit(git, main, entries, entry)
        if admitted == "removed":
            continue  # it merges with no run of main and the entries ahead: the queue removes it
        if admitted is None:  # no queue that keeps it was found: it cannot be checked
            candidate["uncertain"].append(dict(record, kept=[record["number"]], without=[], files=[],
                                               unadmitted=True))
        else:
            blockers[entry["number"]] = admitted[0]
    distinct = list(dict.fromkeys(blockers.values()))
    leaves: list[frozenset] = []  # every union of the blocker sets: any of them may leave first
    for size in range(1, len(distinct) + 1):
        for combination in itertools.combinations(distinct, size):
            union = frozenset().union(*combination)
            if union not in leaves:
                leaves.append(union)
    positions = {e["number"]: e["position"] for e in entries}
    for leave in leaves:
        alternative = _chain(git, main, entries, leave)
        note_pins(alternative)
        kept = [n for n, needed in blockers.items() if needed <= leave and f"#{n}" in alternative["merged"]]
        if not kept:
            continue  # without them, no left-out entry stays
        attempt = git.merge_tree(alternative["tip"], head)
        without = sorted(leave)
        if attempt["clean"]:
            label = "without " + " and ".join(f"#{n}" for n in without)
            candidate["alternatives"][label] = {"base": alternative["tip"], "tree": attempt["tree"],
                                                "entries": alternative["merged"]}
        else:
            candidate["uncertain"].append({"number": kept[0], "position": positions[kept[0]], "kept": kept,
                                           "without": without, "files": attempt["files"]})
    return finish()


def tested_names(git: Git, since: str, head: str) -> set[str] | None:
    """The names that the head adds or moves in the tree its CI built: its merge into `since`, the
    main commit that CI merged it into. None if that merge cannot be reproduced here."""
    merged = git.merge_tree(since, head)
    if not merged["clean"]:
        return None
    changes = git.diff_raw(since, merged["tree"])
    oids = {oid for old, new, _ in changes for oid in (old, new)}
    git.prefetch(oids)
    return set(placed_declarations(changes, git.blobs(oids)))


def find_duplicates(git: Git, main: str, since: str, merges: list[dict], entries: list[dict],
                    changes: dict[str, list[tuple[str, str, str]]], tested: set[str] | None = None) -> dict:
    """Names that merging this pull request adds to, or moves into, a library Lean file, and that the
    merged tree declares twice: in another file that main has changed since `since` or a queued pull
    request changes, or twice in one file.

    Each of `merges` is a merge of this pull request (`after`) onto main and some queued entries
    (`before`). Reading the merged tree takes care of what the merge itself does to the other side's
    files, such as a rename or a changed namespace."""
    parsed: dict[str, list[tuple[str, int]]] = {}  # one parse per blob for the whole scan
    if not any(is_library_lean(path) for merge in merges for _, _, path in git.diff_raw(merge["before"], merge["after"])):
        return {"names": 0, "found": [], "incomplete": None, "unpredictable": []}  # it places no declaration

    def parse(texts: dict[str, str], oid: str) -> list[tuple[str, int]]:
        if oid not in parsed:
            parsed[oid] = declarations(texts[oid])
        return parsed[oid]
    on_main = git.diff_raw(since, main)
    incomplete = None
    if len(on_main) > MAX_MAIN_CHANGES:
        incomplete = f"main changed {len(on_main)} library Lean files since {short(since)}"
    main_paths = {path for _, _, path in on_main}
    entry_paths = {f"#{e['number']}": {path for _, _, path in changes[e["head"]]} for e in entries}
    positions = {f"#{e['number']}": e["position"] for e in entries}
    found, names, unpredictable, untested = [], None, set(), set()
    # What each queued entry's own diff adds, by name: who to blame for a copy.
    own = {f"#{e['number']}": [c for c in changes[e["head"]] if is_library_lean(c[2])] for e in entries}
    own_oids = {oid for diff in own.values() for old, new, _ in diff for oid in (old, new)}
    git.prefetch(own_oids)
    own_texts = git.blobs(own_oids) if own_oids - {ZERO_OID} else {}
    entry_placed = {label: placed_declarations(diff, own_texts, parsed) for label, diff in own.items()}

    versions: dict[str, tuple] = {}  # path -> its declaration counts on main and at `since`

    def main_adds(path: str, name: str) -> bool:
        """Whether main declares `name` in `path` more often than it did at `since`."""
        if path not in main_paths:
            return False
        if path not in versions:
            oids = []
            for commit in (main, since):
                found = git.run("rev-parse", "--verify", "--quiet", f"{commit}:{path}", check=False)
                oids.append(found.stdout.strip() if not found.returncode else "")
            git.prefetch({oid for oid in oids if oid})
            texts = git.blobs({oid for oid in oids if oid}) if any(oids) else {}
            versions[path] = tuple(collections.Counter(n for n, _ in parse(texts, oid)) if oid
                                   else collections.Counter() for oid in oids)
        on_main, before = versions[path]
        return on_main[name] > before[name]
    for merge in merges:
        mine = git.diff_raw(merge["before"], merge["after"])
        start = main if incomplete else since  # what CI did not see: main since its base, and the queue
        theirs = git.diff_raw(start, merge["before"])
        final = {path: new for _, new, path in theirs}
        final.update({path: new for _, new, path in mine})
        oids = {oid for old, new, _ in mine + theirs for oid in (old, new)}
        git.prefetch(oids)
        texts = git.blobs(oids)
        placed = placed_declarations(mine, texts, parsed)
        if names is None:
            names = len([name for name in placed if not name.startswith("?")])
        for name in placed:
            if name.startswith("?gen:"):
                _, attribute, declaration = name.split("#", 1)[0].split(":", 2)
                namespace, command = _split_last(declaration)
                unpredictable.add(f"a field of {declaration} that it cannot read" if attribute == "structure" else
                                  f"a {command} with no (name := ...) in {namespace or 'the root namespace'}"
                                  if attribute == "syntax" else f"@[{attribute}] on {declaration}")
            elif tested is not None and not name.startswith("?") and name not in tested:
                untested.add(name)  # the merge gave it a name or a visibility that its CI did not build

        def source_of(path: str, name: str | None = None) -> str | None:
            """Who put the copy of `name` in `path` there: the queued entry whose own diff adds it there,
            else main if it added it since `since`, else the one entry or main that changed the file,
            else all of those that did."""
            adders = [label for label in merge["entries"]
                      if name and any(p == path for p, _ in entry_placed[label].get(name, []))]
            if adders:
                return adders[0]
            if name and main_adds(path, name):
                return "main"
            touching = [label for label in merge["entries"] if path in entry_paths[label]]
            touching += ["main"] if path in main_paths else []
            return " or ".join(touching) if touching else None

        where: dict[str, list[tuple[str, int]]] = {}
        for path, oid in final.items():
            if oid != ZERO_OID:
                for name, line in parse(texts, oid):
                    if not name.startswith("?") or name.startswith("?local:"):
                        where.setdefault(name, []).append((path, line))
        pairs = [(name, [place for place in places if place[0] == path]) for name, places in placed.items()
                 if name.startswith("?local:") for path in dict.fromkeys(p for p, _ in places)]  # each file apart
        pairs += [(name, places) for name, places in placed.items() if not name.startswith("?local:")]
        for name, ours in pairs:
            copies = where.get(name, [])
            if name.startswith("?local:"):  # module-local: only a second copy in the same file clashes
                copies = [c for c in copies if c[0] == ours[0][0]]
            elif name.startswith("?"):
                continue
            if len(copies) < 2:
                continue
            path, line = ours[0]
            own_files = {p for p, _ in ours}
            others = [(c, source_of(c[0], name)) for c in copies if c != (path, line)]
            # A copy in a file that only this pull request changed is its own; its build fails on that.
            others = [(c, source) for c, source in others if source or c[0] not in own_files]
            if name.startswith("?local:"):  # in one file: only a copy someone else put there
                others = [(c, source) for c, source in others if source]
            if not others:
                continue
            (other_path, other_line), source = others[0]
            record = {"name": name[len("?local:"):] if name.startswith("?local:") else name, "path": path, "line": line,
                      "source": source or "the queue",
                      "other_path": other_path, "other_line": other_line}
            if source in positions:
                record["position"] = positions[source]
            if source == "main":
                change = git.last_change(f"{since}..{main}", (other_path,))
                record["main_pr"] = change and change["pr"]
            if not any((f["name"], f["path"], f["line"]) == (record["name"], record["path"], record["line"]) for f in found):
                found.append(record)  # once, though a public field also counts as a label
        # An anonymous instance's generated name is only approximated, so two new anonymous instances of
        # one class in one namespace count as a possible collision.
        added = placed_declarations(theirs, texts, parsed)
        # A parser named after its syntax is the base or the base with a numeric suffix: a name of that
        # shape on the other side, or another such parser, may be the same declaration.
        def parser_like(base: str, name: str) -> bool:
            """Whether `name` is `base` or `base_<digits>`, in the same namespace."""
            (base_prefix, base_last), (prefix, last) = _split_last(base), _split_last(name)
            return prefix == base_prefix and (last == base_last or bool(re.fullmatch(re.escape(base_last) + r"_\d+", last)))

        def overlap(a: str, b: str) -> bool:  # two parsers' possible names meet
            return parser_like(a, b) or parser_like(b, a)

        theirs_names = {name for name in where} | {n for n in added if not n.startswith("?")}
        for key in placed:
            if key.startswith("?parser:"):
                base = key[len("?parser:"):]
                near = sorted(n for n in theirs_names if parser_like(base, n)) + \
                    [f"another parser named after its syntax ({n[len('?parser:'):]})" for n in added
                     if n.startswith("?parser:") and overlap(base, n[len("?parser:"):])]
                if near:
                    unpredictable.add(f"the parser that a syntax command adds, named {base} or {base}_n, next to {near[0]}")
        # A name that an `attribute` command may generate, its target's namespace aside: a match is
        # possible, not certain.
        # A definition's reserved equation names (`f.eq_1`, ...) may exist wherever it is used: an explicit
        # declaration of one is a possible clash.
        # A parent projection's name when the parent is an alias: `S.toX` for any X, on either side.
        def projection_like(name: str) -> str | None:  # the structure whose projection `name` could be
            plain = name[len("?local:"):] if name.startswith("?local:") else name
            owner, last_part = _split_last(plain)
            return owner if re.fullmatch(r"to[^\W\d_][\w']*", last_part or "") and not name.startswith("?toproj") else None

        def independent(name: str) -> bool:  # placed on the other side, not only by this pull request
            return name in added or any(source_of(path, name) for path, _ in where.get(name, []))
        toproj_added = {n[len("?toproj:"):] for n in added if n.startswith("?toproj:")}
        toproj_placed = {n[len("?toproj:"):] for n in placed if n.startswith("?toproj:")}
        for name in placed:
            if (name[:1] != "?" or name.startswith("?local:")) and projection_like(name) in toproj_added:
                unpredictable.add(f"{name}, which a parent projection of {projection_like(name)} may be named (its parent "
                                  "may be an alias)")
        for name in theirs_names:
            if projection_like(name) in toproj_placed and independent(name):
                unpredictable.add(f"{name}, which a parent projection of {projection_like(name)} may be named (its parent "
                                  "may be an alias)")
        eqns_added = {n[len("?eqns:"):] for n in added if n.startswith("?eqns:")}
        theirs_reserved: dict[str, list[str]] = {}  # owner -> its reserved-looking names on the other side
        for n in theirs_names:
            if _RESERVED.search(n):
                theirs_reserved.setdefault(_RESERVED.sub("", n), []).append(n)
        for name in placed:
            if not name.startswith("?") and _RESERVED.search(name) and _RESERVED.sub("", name) in eqns_added:
                unpredictable.add(f"{name}, a name Lean reserves for the definition {_RESERVED.sub('', name)}")
            elif name.startswith("?eqns:") and name[len("?eqns:"):] in theirs_reserved:
                definition = name[len("?eqns:"):]
                unpredictable.add(f"{sorted(theirs_reserved[definition])[0]}, a name Lean reserves for the definition "
                                  f"{definition}")
        parsers_added = [n[len("?parser:"):] for n in added if n.startswith("?parser:")]
        parsers_placed = [n[len("?parser:"):] for n in placed if n.startswith("?parser:")]
        for key in placed:
            name = key[len("?maybe:"):]
            if key.startswith("?maybe:") and (name in theirs_names or key in added
                                              or any(parser_like(base, name) for base in parsers_added)):
                unpredictable.add(f"{name}, which an attribute command may generate, if its target resolves there")
        for marker, copies in added.items():
            if marker.startswith("?maybe:") and any(parser_like(base, marker[len("?maybe:"):]) for base in parsers_placed):
                unpredictable.add(f"{marker[len('?maybe:'):]}, which an attribute command may generate, next to a parser "
                                  "named after its syntax")
            if marker.startswith("?maybe:") and marker in placed:  # possible on both sides: both may exist
                where_from = source_of(copies[0][0], marker) or "the queue"
                unpredictable.add(f"{marker[len('?maybe:'):]}, which both this pull request and {where_from} may "
                                  "generate")
            if marker.startswith("?maybe:") and marker[len("?maybe:"):] in placed:
                where_from = source_of(copies[0][0], marker) or "the queue"
                unpredictable.add(f"{marker[len('?maybe:'):]}, which an attribute command on {where_from} may "
                                  "generate, if its target resolves there")
        for marker, copies in added.items():
            if marker.startswith("?parser:"):
                base = marker[len("?parser:"):]
                near = sorted(n for n in placed if not n.startswith("?") and parser_like(base, n))
                if near:
                    where_from = source_of(copies[0][0], marker) or "the queue"
                    unpredictable.add(f"the parser that a syntax command on {where_from} adds, named {base} or "
                                      f"{base}_n, next to {near[0]}")
        # Names that the other side's attributes generate, unpredictably, may be those this one adds.
        for marker, copies in added.items():
            if not marker.startswith("?gen:"):
                continue
            _, attribute, declaration = marker.split("#", 1)[0].split(":", 2)
            if attribute == "syntax":  # a parser name made up from its syntax may be any name in that namespace
                namespace, command = _split_last(declaration)
                near = sorted(n for n in placed if (not n.startswith("?") and _split_last(n)[0] == namespace)
                              or (n.startswith("?parser:") and _split_last(n[len("?parser:"):])[0] == namespace))
                if near:
                    where = source_of(copies[0][0], marker) or "the queue"
                    unpredictable.add(f"a {command} with no (name := ...) in {namespace or 'the root namespace'} "
                                      f"({where}), next to {near[0]}")
                continue
            namespace = declaration if attribute == "structure" else _split_last(declaration)[0]
            if attribute == "structure":  # a field label of the same structure, in a file with the marker, any visibility
                matched = False
                for marker_path in dict.fromkeys(path for path, _ in copies):
                    labels = sorted(n[len("?local:"):] for n, places in placed.items() if n.startswith("?local:")
                                    and _split_last(n[len("?local:"):])[0] == namespace
                                    and any(path == marker_path for path, _ in places))
                    if labels:
                        where = source_of(marker_path, marker) or "the queue"
                        unpredictable.add(f"a field of {declaration} that it cannot read ({where}), next to {labels[0]}")
                        matched = True
                if matched:
                    continue
            near = sorted(n for n in placed if (not n.startswith("?") or attribute in ("line", "command")
                                                and n.startswith(("?parser:", "?maybe:"))) and (
                True if attribute in ("line", "command") else  # a command it did not read: any name
                _split_last(n)[0] == namespace
                and (attribute != "simps" or _split_last(n)[1].startswith(_split_last(declaration)[1] + "_"))))
            if near:
                where = source_of(copies[0][0], marker) or "the queue"
                what = f"a field of {declaration} that it cannot read" if attribute == "structure" \
                    else f"@[{attribute}] on {declaration}"
                unpredictable.add(f"{what} ({where}), next to {near[0]}")
        for key, ours in placed.items():
            if not key.startswith("?inst:"):
                continue
            namespace, kind = key[len("?inst:"):].rsplit(":", 1)
            for other, copies in added.items():
                if not other.startswith("?inst:"):
                    continue
                other_namespace, other_kind = other[len("?inst:"):].rsplit(":", 1)
                if other_namespace != namespace or (kind != other_kind and "*" not in (kind, other_kind)):
                    continue
                (path, line), (other_path, other_line) = ours[0], copies[0]
                source = source_of(other_path, other) or "the queue"
                record = {"name": f"an anonymous {'' if kind == '*' else kind + ' '}instance in "
                                  f"{namespace or 'the root namespace'}",
                          "instance": True, "path": path, "line": line, "source": source,
                          "other_path": other_path, "other_line": other_line}
                if source in positions:
                    record["position"] = positions[source]
                if not any((f["path"], f["other_path"]) == (path, other_path) for f in found):
                    found.append(record)
    # A name declared twice brings its generated members along: report the name alone.
    reported = {(f["name"], f["path"], f["other_path"]) for f in found}
    found = [f for f in found if not any((f["name"][:i], f["path"], f["other_path"]) in reported
                                         for i in range(len(f["name"])) if f["name"][i] == ".")]
    if tested is None:
        what = f"the merge of the head into {short(since)} that CI built does not merge cleanly here"
        incomplete = f"{incomplete}; {what}" if incomplete else what
    if untested:
        listed = ", ".join(sorted(untested)[:3]) + (" and more" if len(untested) > 3 else "")
        what = f"merging it gives names that its CI did not build ({listed}); they were not looked up in all of main"
        incomplete = f"{incomplete}; {what}" if incomplete else what
    return {"names": names or 0, "found": found, "incomplete": incomplete, "unpredictable": sorted(unpredictable)}


def gather(gh: GitHub, git: Git, number: int, now: dt.datetime | None = None) -> dict:
    """Everything the verdict depends on, read from GitHub and computed in the clone."""
    pr = get_pull(gh, number)
    head_repo = ((pr.get("head") or {}).get("repo") or {}).get("full_name")
    facts = {"pr": number, "repo": gh.repo, "head": pr["head"]["sha"], "node_id": pr.get("node_id"),
             "title": pr.get("title"), "state": "merged" if pr.get("merged") else pr.get("state"),
             "draft": pr.get("draft"), "base": pr["base"]["ref"], "fork": head_repo != gh.repo,
             "mergeable": pr.get("mergeable"), "mergeable_state": pr.get("mergeable_state"),
             "changed_files": pr.get("changed_files")}
    if facts["state"] != "open" or facts["base"] != "main":
        return facts
    head = facts["head"]
    facts["queue"] = get_queue(gh, facts["base"], number)
    if facts["queue"]["own"]:
        return facts
    reviews = summarize_reviews(gh.paged(f"/repos/{gh.repo}/pulls/{number}/reviews"), head)
    runs = gh.paged(f"/repos/{gh.repo}/commits/{head}/check-runs", "check_runs")
    codex = reviews["codex"]
    if codex and codex["state"] == "APPROVED":
        if codex["kind"] == "automatic":
            codex["attested_by"], codex["search_incomplete"] = codex_attested(gh, runs, codex["id"], number, facts["base"]), False
            if not codex["attested_by"] and head_repo != gh.repo:
                # A fork's automatic review runs on pull_request_target, whose checks attach to main.
                codex["attested_by"], codex["search_incomplete"] = codex_comment_attested(
                    gh, codex, events=("pull_request_target",))
        else:
            codex["attested_by"], codex["search_incomplete"] = codex_comment_attested(gh, codex, head=head)
    facts["reviews"] = reviews
    required = get_required(gh, facts["base"])
    statuses = None
    if any(not c["integration_id"] and c["context"] not in {r.get("name") for r in runs} for c in required):
        statuses = gh.get(f"/repos/{gh.repo}/commits/{head}/status").get("statuses")
    git.ensure()
    git.size_oracle = lambda oids: blob_sizes(gh, oids)
    git.fetch([f"+refs/heads/{facts['base']}:refs/preflight/main"])
    main = git.rev_parse("refs/preflight/main")  # the one main that the checks, the simulation and enqueue use
    workflows, unreadable = workflow_jobs(git, main)
    provenance = Provenance(gh, number, facts["base"], workflows=workflows, unreadable=unreadable)
    facts["check_workflows"] = sorted({path for context in [c["context"] for c in required] + [CI_CHECK]
                                       for path in workflows.get(context, ())} | unreadable)
    facts["code_by_workflow"] = {path: workflow_code(git, main, [path]) for path in facts["check_workflows"]}
    facts["check_code"] = sorted({c for code in facts["code_by_workflow"].values() for c in code})
    git.watched = frozenset(facts["check_code"]) | frozenset(facts["check_workflows"])
    facts["check_roots"] = code_roots(facts["check_code"], lambda entry: code_signature(git, main, entry) is not None)
    facts["checks"] = summarize_checks(runs, required, statuses, provenance)
    facts["ci"] = ci_run(gh, runs, head, number, facts["base"], provenance)
    compute(git, facts, number, head, main)
    facts["stale_checks"] = stale_checks(gh, git, main, facts["checks"]["required"], provenance, facts["base"], now,
                                         facts.get("code_by_workflow"))
    # Last, after every read that decides: an advisory warning's two requests.
    facts["build_time"] = build_time(gh, next((c for c in facts["checks"]["required"] if c["name"] == CI_CHECK), None))
    return facts


def _attribute_list(text: str) -> tuple[str, str] | None:
    """An `attribute` command's `[...]` list and the text after it, brackets inside `«...»` aside; None
    while the list is still open (or there is none)."""
    start = text.find("[")
    if start < 0 or text[:start].strip():
        return None
    depth, quoted = 0, False
    for index in range(start, len(text)):
        char = text[index]
        if char in "«»":
            quoted = char == "«"
        elif not quoted and char == "[":
            depth += 1
        elif not quoted and char == "]":
            depth -= 1
            if depth == 0:
                return text[start + 1:index], text[index + 1:]
    return None


def _open_list(text: str) -> bool:
    """Whether an `attribute` command's `[...]` list is still open."""
    return "[" in text and _attribute_list(text) is None


def _update_chain(updates: list[tuple]) -> list[tuple] | None:
    """`updates` (time, before, after) in the order main took them, linked by before and after; None
    unless they form one chain."""
    afters = {u[2] for u in updates}
    starts = [u for u in updates if u[1] not in afters]
    if len(starts) != 1:
        return None
    by_before = {u[1]: u for u in updates}
    order = starts
    while order[-1][2] in by_before and len(order) < len(updates):
        order = order + [by_before[order[-1][2]]]
    return order if len(order) == len(updates) else None


def blob_sizes(gh: GitHub, oids: list[str]) -> dict[str, int | None]:
    """The size of each blob, as GitHub reports it without sending it (None if it says nothing)."""
    owner, name = gh.repo.split("/", 1)
    sizes: dict[str, int | None] = {}
    for start in range(0, len(oids), 100):
        batch = oids[start:start + 100]
        fields = " ".join(f'b{i}: object(oid: "{oid}") {{ ... on Blob {{ byteSize }} }}' for i, oid in enumerate(batch))
        data = graphql_data(gh.graphql(f'query {{ repository(owner: "{owner}", name: "{name}") {{ {fields} }} }}', {}),
                            "blob sizes")
        repository = data.get("repository") or {}
        sizes.update({oid: (repository.get(f"b{i}") or {}).get("byteSize") for i, oid in enumerate(batch)})
    return sizes


def build_time(gh: GitHub, build: dict | None) -> dict | None:
    """How long this pull request's own successful CI run took (`build`: the required check as
    summarize_checks authenticated it, whose workflow run is read), in minutes, beside the median of the
    last BUILD_SAMPLE successful pull request runs of that workflow: two requests. It only feeds a
    warning: nothing here fails the run, and without the history the absolute threshold still applies."""
    def span(start: str | None, end: str | None) -> float | None:
        try:
            begun, ended = parse_time(start), parse_time(end)
        except (ValueError, TypeError, AttributeError):
            return None
        return (ended - begun).total_seconds() / 60 if begun and ended and ended >= begun else None
    if not build or build.get("conclusion") != "success" or build.get("provenance") == "unknown":
        return None
    own, recent = span(build.get("started_at"), build.get("completed_at")), []
    try:
        run = gh.get(f"/repos/{gh.repo}/actions/runs/{int(build['run'])}")
        own = span(run.get("run_started_at"), run.get("updated_at")) or own  # the whole run, as the history has it
        workflow = (run.get("path") or "").split("@", 1)[0].rsplit("/", 1)[-1]
        listed = gh.get(f"/repos/{gh.repo}/actions/workflows/{workflow}/runs?event=pull_request"
                        f"&status=success&per_page={BUILD_SAMPLE}") if workflow else {}
        recent = [m for r in (listed.get("workflow_runs") or [])[:BUILD_SAMPLE]
                  if (m := span(r.get("run_started_at"), r.get("updated_at"))) is not None]
    except Exception:  # an unreadable or cut answer: the history is unknown, the verdict unaffected
        recent = []
    if own is None:
        return None
    return {"minutes": own, "median": statistics.median(recent) if recent else None, "sample": len(recent)}


def stale_checks(gh: GitHub, git: Git, main: str, required: list[dict], provenance: Provenance,
                 base_ref: str = "main", now: dt.datetime | None = None,
                 code_by_workflow: dict[str, list[str]] | None = None) -> list[dict]:
    """The required checks whose run used another copy of its workflow than main has now. Main as it was
    when the run started comes from the repository's activity on the branch, which times every update
    of it to the second (`time_period=day`: the last 24 hours): the state before the first update after
    the run started, or the newest state if none came after. Updates in the very second the run started
    leave its order open, so if the workflow differs across them the check's freshness is unknown, as it
    is when the run's start, its workflow or main's history cannot be read."""
    now = now or dt.datetime.now(dt.timezone.utc)
    out, updates = [], None
    for check in required:
        if check.get("status") != "completed" or not check.get("run"):
            continue
        run = provenance.run(check["run"]) or {}
        path = (run.get("path") or "").split("@", 1)[0]
        if not path or not run.get("created_at"):
            out.append({"name": check["name"], "unknown": "its run does not say when it started or what it ran"})
            continue
        if updates is None:
            try:
                updates = sorted((parse_time(a["timestamp"]), a["before"], a["after"]) for a in gh.paged(
                    f"/repos/{gh.repo}/activity?ref=refs/heads/{base_ref}&time_period=day"))
            except (Failure, KeyError, TypeError, ValueError):
                updates = False  # unread: nothing can be told
        started = parse_time(run["created_at"])
        if updates is False or started < now - dt.timedelta(hours=23):
            out.append({"name": check["name"], "unknown": "main's history does not cover when its run started"})
            continue
        tied = [u for u in updates if u[0] == started]
        later = [u for u in updates if u[0] > started]
        if tied:  # its place among the updates of that second is open: main may have been at any of them
            states = [u[1] for u in tied] + [u[2] for u in tied]
        elif later:  # the state before the first update after it, in main's order within that second
            first = [u for u in later if u[0] == later[0][0]]
            order = _update_chain(first)
            states = [order[0][1]] if order else [u[1] for u in first] + [u[2] for u in first]
        else:  # the newest state, in main's order within its second
            last = [u for u in updates if u[0] == updates[-1][0]] if updates else []
            order = _update_chain(last)
            states = [order[-1][2]] if order else [u[2] for u in last] or [main]

        def blob(commit: str, file: str) -> str | None:  # a directory gives its tree, a glob what it matches
            return code_signature(git, commit, file)
        if not all(git.rev_parse(state) for state in states):
            out.append({"name": check["name"], "unknown": "main's history names a commit this clone does not have"})
            continue
        code = list((code_by_workflow or {}).get(path, []))
        if "?incomplete" in code:
            out.append({"name": check["name"], "unknown": "the code its workflow runs is too large to follow"})
            continue
        for file in [path] + code:  # the workflow and the code it runs (a directory compares as a whole)
            copies = {blob(state, file) for state in states}
            if len(copies) > 1:
                out.append({"name": check["name"], "unknown": f"main changed {file} in the second its run started"})
                break
            if copies != {blob(main, file)}:
                out.append({"name": check["name"], "path": file, "main": states[0]})
                break
    return out


SELF = "scripts/queue/preflight.py"


def on_first_parent(git: Git, commit: str, main: str) -> bool:
    """Whether `commit` was once main itself: it is on the first-parent history of `main`."""
    steps = int(git.out("rev-list", "--count", "--first-parent", f"{commit}..{main}"))
    return git.rev_parse(f"{main}~{steps}") == git.rev_parse(commit)


def copy_differs(git: Git, main: str) -> bool | None:
    """Whether this file differs from main's copy of it; None if main has none."""
    found = git.run("rev-parse", "--verify", "--quiet", f"{main}:{SELF}", check=False)
    on_main = found.stdout.strip()
    if found.returncode or not on_main:
        return None
    return git.out("hash-object", "--", str(Path(__file__).resolve())) != on_main


def compute(git: Git, facts: dict, number: int, head: str, main: str) -> None:
    """Add the facts computed in the clone against `main`, as fetched once: freshness, the queue
    simulation, duplicates."""
    entries = [e for e in facts["queue"]["entries"] if e["number"] != number and e["head"]]
    git.fetch([f"+refs/pull/{number}/head:refs/preflight/pr/{number}"]
              + [f"+refs/pull/{e['number']}/head:refs/preflight/pr/{e['number']}" for e in entries])
    missing = [sha for sha in [head] + [e["head"] for e in entries] if not git.rev_parse(sha)]
    if missing:  # a head moved after the API read: fetch the exact commits
        git.fetch(missing)
    facts["main"] = main
    facts["copy_differs"] = copy_differs(git, main)
    facts["contains_queued"] = [e["number"] for e in entries if git.is_ancestor(e["head"], head)]
    changes = head_changes(git, main, [head] + [e["head"] for e in entries])
    facts["files"] = [path for _, _, path in changes[head]]
    ci = facts.get("ci") or {}
    base = ci.get("base")
    if base and not (git.rev_parse(base) and git.is_ancestor(base, main)):
        ci["base_error"], ci["base"], base = f"its base {short(base)} is not on main", None, None
    elif base and not on_first_parent(git, base, main):  # e.g. the tip of a stack's lower branch
        ci["base_error"], ci["base"], base = (f"its base {short(base)} was never main itself (it is not on main's "
                                              "first-parent history)"), None, None
    pins = git.last_change(main, PIN_FILES)
    if pins:
        pins["in_base"] = git.is_ancestor(pins["commit"], base) if base else None
    facts["pins"] = pins
    if base:
        ci["main_moved"] = int(git.out("rev-list", "--count", "--first-parent", f"{base}..{main}"))
    simulation = simulate(git, main, entries, head, changes)
    facts["simulation"] = simulation

    def blob(tree: str, path: str) -> str | None:  # a directory gives its tree, a glob what it matches
        return code_signature(git, tree, path)
    merged = simulation["main"]["tree"]  # the candidate merged into main: what its merge would change
    tested = git.merge_tree(base, head)["tree"] if base else None  # the merge that CI ran
    facts["codex_workflow_changed"] = CODEX_WORKFLOW in facts["files"] \
        or blob(merged, CODEX_WORKFLOW) != blob(main, CODEX_WORKFLOW) \
        or bool(tested and blob(tested, CODEX_WORKFLOW) != blob(base, CODEX_WORKFLOW))
    facts["changed_workflows"], facts["stale_workflows"] = [], []
    for path in facts.get("check_workflows") or []:
        now = blob(merged, path)
        if now != blob(main, path) or (tested and blob(tested, path) != blob(base, path)):
            facts["changed_workflows"].append(path)  # the candidate changes it: its runs used its own copy
        elif tested and blob(tested, path) != now:
            facts["stale_workflows"].append(path)  # main has changed it since CI ran: CI ran an older copy
    facts["workflows_ahead"] = []  # each entry that may be in the merge group and changes one
    watched = list(facts.get("check_workflows") or []) + [c for c in facts.get("check_code") or [] if c != "?incomplete"]
    for e in entries:
        differing = [path for path in watched if blob(e["head"], path) != blob(main, path)]
        tree = git.merge_tree(main, e["head"])["tree"] if differing else None
        facts["workflows_ahead"] += [{"number": e["number"], "position": e["position"], "path": path}
                                     for path in differing if blob(tree, path) != blob(main, path)]
    # Code that the required checks run (scripts, local actions), and this script: changed by the candidate,
    # its runs used its own copy.
    roots = tuple(f"{root}/" for root in facts.get("check_roots") or [])
    touched = {path for _, _, path in git.diff_raw(main, merged, ())}  # every file, not only Lean ones
    if tested:
        touched |= {path for _, _, path in git.diff_raw(base, tested, ())}
    named = {c for c in facts.get("check_code") or [] if re.search(_SCRIPT, c)}  # scripts the checks run, by name
    facts["changed_dependencies"] = sorted(path for path in touched if ((roots and path.startswith(roots)) or path in named)
                                           and path not in (facts.get("check_workflows") or []))
    facts["changes_self"] = SELF in touched
    if "?incomplete" in (facts.get("check_code") or []):
        facts["stale_workflows"].append("?incomplete")  # code that the checks run but preflight could not follow
    for path in [c for c in facts.get("check_code") or [] if c != "?incomplete"]:
        now = blob(merged, path)
        if path in facts["changed_dependencies"]:
            continue  # the candidate's own change: the hand check above
        if tested and blob(tested, path) != now:
            facts["stale_workflows"].append(path)  # main changed it after CI ran: CI ran an older copy
    candidate = simulation.get("candidate") or {}
    tips = [simulation.get("tip")] + [a["base"] for a in (candidate.get("alternatives") or {}).values()] \
        + [(candidate.get("partial") or {}).get("base")]  # every queue ahead the merge group may have
    named = {a["path"] for a in facts["workflows_ahead"]}
    facts["workflows_ahead"] += [{"number": None, "position": None, "path": path}
                                 for path in watched
                                 if path not in named and any(tip and blob(tip, path) != blob(main, path) for tip in tips)]
    since = base or git.merge_base(main, head) or main
    facts["duplicates"] = find_duplicates(git, main, since, merges_to_read(simulation, main), entries, changes,
                                          tested_names(git, since, head))


def merges_to_read(simulation: dict, main: str) -> list[dict]:
    """The merges of the candidate that the duplicate check reads: onto the whole queue (or, when it
    conflicts with an entry, onto the entries ahead of that one), and onto main and each entry that the
    queue may keep despite a conflict."""
    candidate = simulation["candidate"] or {}
    clean = [f"#{e['number']}" for e in simulation["entries"] if e["clean"]]
    if candidate.get("clean"):
        merges = [{"before": simulation["tip"], "after": candidate["tree"], "entries": clean}]
    elif candidate.get("partial"):  # it conflicts with an entry: read the merge onto the entries ahead of it
        partial = candidate["partial"]
        merges = [{"before": partial["base"], "after": partial["tree"], "entries": partial["entries"]}]
    else:
        return []
    for alternative in candidate.get("alternatives", {}).values():
        merges.append({"before": alternative["base"], "after": alternative["tree"], "entries": alternative["entries"]})
    return merges


# --------------------------------------------------------------------------------------------------
# The verdict


def evaluate(facts: dict, now: dt.datetime, max_age_hours: float = DEFAULT_MAX_AGE_HOURS,
             max_files: int = DEFAULT_MAX_FILES) -> dict:
    """READY or NOT READY, with one entry per check, the warnings, and the next thing to do."""
    checks: list[dict] = []
    warnings: list[str] = []

    def check(name: str, ok: bool, detail: str, next_step: str | None = None, items: list | None = None,
              provenance_only: bool = False, hand_check: bool | str = False):
        checks.append({"name": name, "ok": ok, "detail": detail, "items": items or [],
                       "next": None if ok else next_step, "provenance_only": provenance_only and not ok,
                       "hand_check": hand_check if not ok else False})

    def verdict() -> dict:
        fork = facts.get("fork")
        if fork:  # never READY, never queued by preflight: see the atlas-merge-queue skill
            check("fork", False, "a fork's pull request: GitHub does not say which pull request a fork's runs "
                  "tested, so preflight cannot vouch for its checks and does not queue it", hand_check=True)
        ready = all(c["ok"] for c in checks)
        failing = [c for c in checks if not c["ok"]]
        if failing and all(c.get("hand_check") or (fork and c.get("provenance_only")) for c in failing):
            what = (["its required checks and CI run, on its page"] if fork else []) + \
                   [c["hand_check"] for c in failing if isinstance(c.get("hand_check"), str)]
            next_step = (f"only hand checks remain: a maintainer checks {'; '.join(what)}, then queues it from the "
                         "merge box and says so in the pull request (see the atlas-merge-queue skill)")
        else:
            next_step = next((c["next"] for c in failing if c["next"] and not c.get("provenance_only")), None) \
                or next((c["next"] for c in failing if c["next"]), None)
        if ready:
            if facts.get("copy_differs") is False:  # this copy is main's: name it, wherever the caller is
                next_step = f"queue it: python3 -I {shlex.quote(str(Path(__file__).resolve()))} {facts['pr']} --enqueue"
            else:
                next_step = (f"queue it with main's copy of preflight, from a clean checkout of main: python3 -I "
                             f"<main-checkout>/{SELF} {facts['pr']} --enqueue (see the atlas-merge-queue skill)")
            if warnings:
                next_step += ", at a quiet hour (see the warnings)"
        return {"pr": facts["pr"], "head": facts["head"], "verdict": "READY" if ready else "NOT READY",
                "ready": ready, "checks": checks, "warnings": warnings, "next": next_step, "facts": facts}

    # 1. State
    if facts["state"] != "open":
        check("state", False, f"the pull request is {facts['state']}", "nothing to do")
        return verdict()
    if facts["base"] != "main":
        check("state", False, f"it targets {facts['base']}, not main; preflight checks only pull requests that "
              "target main, so it cannot check a stack, whose top head is what the queue builds",
              "land the pull requests below it first, then retarget it to main and run preflight again")
        return verdict()
    own = facts["queue"].get("own")
    if own:
        check("state", False, f"it is already in the merge queue, at position {own.get('position')} "
              f"({own.get('state')})", "nothing to do; do not push to it, which removes it from the queue")
        return verdict()
    simulation, head = facts["simulation"], facts["head"]
    if facts["draft"]:
        check("state", False, "it is a draft", "mark it ready for review when it is done")
    elif facts["mergeable"] is False:
        check("state", False, f"GitHub finds a conflict with main ({facts['mergeable_state']})",
              "merge main into the branch, resolve the conflicts, push, and wait for CI and Codex")
    elif facts["mergeable"] is None:
        local = "clean" if simulation["main"]["clean"] else "in conflict"
        check("state", False, f"GitHub has not computed whether it is mergeable yet (a local merge with main "
              f"is {local})", "run preflight again in a few minutes")
    else:
        check("state", True, "open, ready for review, mergeable")

    # 2. Codex and reviewers
    reviews = facts["reviews"]
    codex, latest = reviews["codex"], reviews.get("codex_latest")
    files = facts.get("files") or []
    if reviews["change_requests"]:
        check("codex", False, "changes requested by " + ", ".join(
            f"{r['login']} (on {short(r['commit'])})" for r in reviews["change_requests"]),
            "address the requested changes, then ask the reviewer to review again")
    elif codex and codex["state"] == "APPROVED" and not codex.get("attested_by"):
        where = ("on the head" if codex["kind"] == "automatic"
                 else "in the Codex runs that comments started before it")
        if codex.get("search_incomplete"):
            check("codex", False, f"Codex approved {short(head)}, but there were too many Codex runs to find the "
                  f"one that posted review {codex['id']}", "run preflight again; if this persists, comment "
                  "`@codex` in the pull request's conversation for a new review")
        else:
            check("codex", False, f"Codex approved {short(head)}, but no codex-verdict job {where} names review "
                  f"{codex['id']}", "wait for the Codex workflow to finish; if no codex-verdict job names the "
                  "review, comment `@codex` in the pull request's conversation")
    elif codex and codex["state"] == "APPROVED" and facts.get("codex_workflow_changed", CODEX_WORKFLOW in files) \
            and codex["attested_by"] not in ("issue_comment", "pull_request_target"):
        check("codex", False, f"it changes {CODEX_WORKFLOW}, and the run that approved it "
              f"({codex['attested_by']}) used that changed workflow", "comment `@codex` in the pull request's "
              "conversation, not on a line of the diff: that review runs main's workflow")
    elif codex and codex["state"] == "APPROVED":
        how = "" if codex["kind"] == "automatic" else ", in a review that `@codex` requested"
        check("codex", True, f"Codex approved {short(head)} at {codex['submitted_at']}{how}")
    elif codex and codex["state"] == "CHANGES_REQUESTED":
        check("codex", False, f"Codex requested changes on {short(head)}",
              "fix Codex's findings, push, and wait for CI and Codex")
    else:
        older = f"; its latest formal review is of {short(latest['commit'])}" if latest else ""
        step = ("wait for Codex's review of the head, which follows a push within minutes; if none comes, "
                "comment `@codex` on the pull request")
        if facts.get("fork"):
            step = ("ask a maintainer: Codex reviews a fork's pull request formally only for the authors and "
                    "head owners that codex.yml trusts, and an advisory review does not count")
        check("codex", False, f"no formal Codex verdict on {short(head)} yet{older}", step)

    # 3. Required checks
    required = facts["checks"]["required"]
    failed = [c for c in required if c["status"] == "completed" and c["conclusion"] != "success"]
    unknown = [c for c in required if c.get("provenance") == "unknown" or c["status"] == "unknown"]
    pending = [c for c in required if c["status"] not in ("completed", "unknown")]
    untied = (None if facts.get("fork") else  # the fork check says what to do
              "re-run those checks on this pull request (or merge main, push, and wait for CI and Codex), then "
              "run preflight again")
    if failed or unknown:
        details, fix = [], None
        if pending:
            details.append(f"not finished on {short(head)}: " + ", ".join(
                c["name"] + ("" if c["status"] else " (not reported)") for c in pending))
            fix = "wait for the required checks; advisory checks such as Blueprint Pages need no waiting"
        if failed:
            details.append(f"failed on {short(head)}: " + ", ".join(f"{c['name']} ({c['conclusion']})" for c in failed))
            fix = "read the failing step, fix it, push, and wait for CI and Codex"
            if all(c["conclusion"] in ("cancelled", "stale", "startup_failure") for c in failed):
                fix = "re-run the cancelled workflow; if it fails again, " + fix
            details.insert(0, details.pop())  # the known failure first
        if unknown:
            details.append(f"the latest run of {', '.join(c['name'] for c in unknown)} on {short(head)} cannot be "
                           "tied to this pull request")
            fix = fix or untied
        check("required checks", False, "; ".join(details), fix, provenance_only=not failed and not pending)
    elif pending:
        check("required checks", False, f"not finished on {short(head)}: " + ", ".join(
            c["name"] + ("" if c["status"] else " (not reported)") for c in pending),
            "wait for the required checks; advisory checks such as Blueprint Pages need no waiting")
    else:
        check("required checks", True, ", ".join(c["name"] for c in required) + " passed")
    for name in facts["checks"]["advisory_failed"]:
        warnings.append(f"the advisory check `{name}` failed on this head")

    # 4. Freshness
    ci, pins = facts.get("ci"), facts.get("pins")
    problems, notes, step = [], [], REFRESH
    untied = bool(ci) and not ci.get("created_at") and "cannot be tied" in (ci.get("base_error") or "")
    if untied:
        problems.append(f"its latest CI `{CI_CHECK}` run on {short(head)} cannot be tied to this pull request")
        step = None if facts.get("fork") else "re-run CI on this pull request, then run preflight again"
    elif not ci or not ci.get("created_at"):
        problems.append(f"no CI `{CI_CHECK}` run found on {short(head)}")
        step = "wait for CI to run on the head"
    else:
        age = (now - parse_time(ci["created_at"])).total_seconds() / 3600
        base = ci.get("base")
        if not base:
            problems.append(f"which main CI merged it into is unknown: {ci.get('base_error')}")
            step = f"run preflight again once CI has finished; if its log stays unreadable, {REFRESH}"
        elif pins and pins.get("in_base") is False:
            name = f"#{pins['pr']}" if pins.get("pr") else short(pins["commit"])
            problems.append(f"CI merged it into main {short(base)}, which predates {name}'s change to the pins")
        for path in facts.get("stale_workflows") or []:
            problems.append(f"the code that the required checks run is too large for preflight to follow" if path == "?incomplete"
                            else f"CI ran its required checks with {path} as it was on main {short(base)}; main has "
                            "changed it since")
        if age > max_age_hours:
            problems.append(f"CI ran on this head {age:.1f} hours ago, more than {max_age_hours:g}")
        notes.append(f"CI merged it into main {short(base)} {age:.1f} hours ago" if base
                     else f"CI ran {age:.1f} hours ago")
        if ci.get("main_moved") is not None:
            notes.append(f"main has taken {ci['main_moved']} merges since")
    provenance_only = untied and len(problems) == 1
    for stale in facts.get("stale_checks") or []:
        if stale.get("unknown"):
            problems.append(f"which copy of its workflow {stale['name']} ran is unknown: {stale['unknown']}")
            step = f"run preflight again; if this persists, {REFRESH}"
        else:
            problems.append(f"{stale['name']} ran on main {short(stale['main'])}, and main has changed {stale['path']} since")
            step = REFRESH
        provenance_only = False
    for ahead in facts.get("workflows_ahead") or []:  # whatever CI shows
        if ahead.get("number"):
            problems.append(f"#{ahead['number']}, queued at position {ahead['position']}, changes {ahead['path']}, "
                            "and CI has not run this head's required checks with it")
            step = f"wait for #{ahead['number']} to land, then {REFRESH}"
        else:
            problems.append(f"the queue ahead changes {ahead['path']}, and CI has not run this head's required "
                            "checks with it")
            step = f"wait for the pull requests queued ahead of it to land, then {REFRESH}"
        provenance_only = False
    for change in simulation["pin_changes_ahead"]:  # whatever CI shows
        problems.append(f"#{change['number']}, queued at position {change['position']}, changes "
                        f"{', '.join(change['files'])}, and CI has not tested this head on that")
        step = f"wait for #{change['number']} to land, then {REFRESH}"
        provenance_only = False
    if problems:
        check("freshness", False, "; ".join(notes) if notes else "no CI run", step, problems,
              provenance_only=provenance_only)
    else:
        check("freshness", True, "; ".join(notes))

    # 5. Conflicts
    merged = [e for e in simulation["entries"] if e["clean"]]
    for entry in simulation["entries"]:
        if not entry["clean"]:
            warnings.append(f"queued #{entry['number']} conflicts with the entries ahead of it "
                            f"({', '.join(entry['files'][:3])}); the queue will remove it")
    candidate = simulation["candidate"]
    if facts.get("contains_queued"):
        numbers = " and ".join(f"#{n}" for n in facts["contains_queued"])
        check("conflicts", False, f"it contains the commits of {numbers}, which the queue holds, so the queue would "
              "remove it (invalid merge commit)", f"wait for {numbers} to land, then merge main into the branch, "
              "push, and wait for CI and Codex")
    elif not simulation["main"]["clean"]:
        check("conflicts", False, "conflicts with main", "merge main into the branch, resolve the conflicts, "
              "push, and wait for CI and Codex", simulation["main"]["files"][:10])
    elif not candidate["clean"] and candidate["conflicts_with"]:
        other = candidate["conflicts_with"]
        check("conflicts", False, f"merges cleanly with main but conflicts with #{other['number']}, queued at "
              f"position {other['position']}", f"wait for #{other['number']} to land, then merge main, "
              "resolve the conflicts, push, and wait for CI and Codex", other["files"][:10])
    elif not candidate["clean"]:
        check("conflicts", False, "conflicts with the queued pull requests taken together",
              "wait for the queue to drain, then merge main, resolve the conflicts, and push",
              candidate["files"][:10])
    elif candidate.get("unexplored"):
        check("conflicts", False, f"{candidate['unexplored']} queued pull requests conflict with entries ahead of "
              f"them, more than the {MAX_LEFT_OUT} whose alternatives preflight explores",
              "wait until the queue has removed them, then run preflight again")
    elif candidate.get("uncertain") and candidate["uncertain"][0].get("unadmitted"):
        other = candidate["uncertain"][0]
        check("conflicts", False, f"#{other['number']}, queued at position {other['position']} and left out now for "
              "a conflict, stays queued if the entries it conflicts with leave first; preflight found no such "
              "queue to test this pull request against", f"wait until #{other['number']} has left the queue or "
              "landed, then run preflight again")
    elif candidate.get("uncertain"):
        other = candidate["uncertain"][0]
        kept = " and ".join(f"#{n}" for n in other["kept"])
        without = " and ".join(f"#{n}" for n in other["without"])
        check("conflicts", False, f"merges cleanly with the queue as it stands, but not with the queue without "
              f"{without}, which keeps {kept} queued (left out now for a conflict)",
              f"wait until {kept} has left the queue or landed, then run preflight again", other["files"][:10])
    else:
        skipped = len(simulation["entries"]) - len(merged)
        check("conflicts", True, f"merges cleanly with main and the {len(merged)} queued pull requests ahead"
              + (f" that merge with each other ({skipped} conflict and will be removed)" if skipped else ""))

    # 6. Duplicate declarations
    duplicates = facts["duplicates"]
    items, step = [], None
    for d in duplicates["found"]:
        if d["source"] == "main":
            where = "main" + (f" (last changed by #{d['main_pr']})" if d.get("main_pr") else "")
        elif "position" in d:
            where = f"{d['source']}, queued at position {d['position']},"
        else:
            where = d["source"]
        if d.get("instance"):
            items.append(f"{d['name']} ({d['path']}:{d['line']}) may get the same generated name as one that "
                         f"{where} adds in {d['other_path']}:{d['other_line']}")
            step = step or ("give the instance an explicit name (`instance instName : ...`), push, and wait for "
                            "CI and Codex")
        else:
            items.append(f"{d['name']} ({d['path']}:{d['line']}) is also declared on {where} in "
                         f"{d['other_path']}:{d['other_line']}")
            step = step or (f"{REFRESH}; import main's declaration instead of declaring the name again"
                            if d["source"] == "main" else
                            f"wait for {d['source']} to land, then merge main, import its declaration instead of "
                            "declaring the name again, push, and wait for CI and Codex")
    if duplicates.get("incomplete"):
        items.append(f"not compared with main: {duplicates['incomplete']}")
        step = step or REFRESH
    if duplicates.get("unpredictable"):
        listed = ", ".join(duplicates["unpredictable"][:3]) + (" and more" if len(duplicates["unpredictable"]) > 3 else "")
        items.append(f"not checked: names that Lean generates for {listed}")
        step = step or ("check by hand that neither the queued pull requests nor main since the CI run declare "
                        "those generated names")
    if items:
        hand = (f"that neither the queued pull requests nor main since the CI run declare the names Lean generates "
                f"for {listed}" if duplicates.get("unpredictable") and not duplicates["found"]
                and not duplicates.get("incomplete") else False)  # the one problem left is a hand check
        check("duplicates", False, f"{len(duplicates['found'])} of the declarations it adds or moves are also "
              "added elsewhere" + ("; the check is incomplete" if duplicates.get("incomplete")
                                   or duplicates.get("unpredictable") else ""),
              step, items, hand_check=hand)
    else:
        check("duplicates", True, f"none of the {duplicates['names']} names it adds or moves is added elsewhere"
              if duplicates["names"] else "it adds or moves no declarations")

    # The workflows behind the required checks: a pull request's runs use its own copy of them.
    supplying = facts["changed_workflows"] if "changed_workflows" in facts else \
        [f for f in files if f in (facts.get("check_workflows") or [])]
    supplying = supplying + (facts.get("changed_dependencies") or [])
    if supplying:
        listed = ", ".join(supplying[:3]) + (f" and {len(supplying) - 3} more" if len(supplying) > 3 else "")
        check("workflows", False, f"it changes {listed}, which the required checks run: its runs on this pull "
              "request use its own copy, so they cannot vouch for it",
              "have a maintainer review the change", hand_check=f"the change to {listed}")
    if facts.get("changes_self"):
        check("preflight", False, f"it changes {SELF}: once merged, preflight runs that code with a maintainer's "
              "token", "have a maintainer review the change", hand_check=f"the change to {SELF}")

    # Warnings
    queue_length = len(facts["queue"]["entries"])
    risky = []
    hubs = [f for f in files if f in HUB_MODULES]
    if hubs:
        risky.append(f"it changes {', '.join(hubs)}, which about 1,900 modules import")
    heavy = sorted({f for f in files for prefix in HEAVY_MODULES if f.startswith(prefix)})
    if heavy:
        risky.append(f"it changes {', '.join(heavy[:4])}{' and more' if len(heavy) > 4 else ''}, "
                     "which take minutes to build")
    count = facts.get("changed_files") or len(files)
    if count > max_files:
        risky.append(f"it changes {count} files, more than {max_files}, so it is likelier to conflict")
    if any(f in PIN_FILES for f in files):
        risky.append("it changes the Lean or dependency pins: follow docs/BUMPS.md")
    for item in risky:
        warnings.append(f"{item}; queue it at a quiet hour or when the queue is short (it has {queue_length} "
                        "entries now), so that few builds restart behind it if it fails")
    built = facts.get("build_time") or {}
    if built.get("minutes") is not None and (built["minutes"] > HEAVY_BUILD_MINUTES or (
            built.get("median") and built["minutes"] > HEAVY_BUILD_FACTOR * built["median"])):
        against = (f", against a median of {built['median']:.0f} min over the last {built['sample']} pull request "
                   "runs") if built.get("median") else ""
        warnings.append(f"a heavy rebuild: its CI run took {built['minutes']:.0f} min{against}. Every merge group "
                        f"behind it includes its changes, so each waits for that rebuild and does it again: queue it "
                        f"when the queue is short (it has {queue_length} entries now)")
    workflows = [f for f in files if f.startswith(".github/workflows/") and f not in supplying]
    if workflows:
        warnings.append(f"it changes {', '.join(workflows[:3])}, and a pull request's checks run its own "
                        "workflows: have a maintainer review them")
    if facts.get("copy_differs"):
        warnings.append(f"this copy of {SELF} differs from main's: run main's copy, from a clean checkout of "
                        "main (see the atlas-merge-queue skill); --enqueue will not queue from this one")
    return verdict()


def enqueue(gh: GitHub, result: dict) -> dict:
    """Queue a READY pull request, pinned to its head, unless main or the queue changed since they were read."""
    if not result["ready"]:
        return {"ok": False, "error": "not queued: the verdict is NOT READY"}
    facts = result["facts"]
    if facts.get("fork"):
        return {"ok": False, "error": "not queued: a fork's pull request is queued from its merge box, after a "
                                      "maintainer's hand check (see the atlas-merge-queue skill)"}
    if facts.get("copy_differs") is not False:
        why = "differs from main's" if facts.get("copy_differs") else "could not be checked against main's"
        return {"ok": False, "error": f"not queued: this copy of {SELF} {why}; run main's copy, from a clean "
                                      "checkout of main (see the atlas-merge-queue skill)"}
    checked = [(e["number"], e["head"]) for e in facts["queue"]["entries"] if e["number"] != facts["pr"]]
    queue = get_queue(gh, facts["base"], facts["pr"])
    now = [(e["number"], e["head"]) for e in queue["entries"] if e["number"] != facts["pr"]]
    why = ("it is queued already" if queue["own"] else
           f"main moved from {short(facts['main'])} to {short(queue['main'])}" if queue["main"] != facts["main"] else
           "the queue changed" if now != checked else None)
    if not why:
        pr = gh.get(f"/repos/{gh.repo}/pulls/{facts['pr']}")
        reviews = summarize_reviews(gh.paged(f"/repos/{gh.repo}/pulls/{facts['pr']}/reviews"), facts["head"])
        checked_codex = facts["reviews"]["codex"] or {}
        codex = reviews["codex"] or {}
        if pr["head"]["sha"] != facts["head"] or pr.get("state") != "open" or pr.get("draft") \
                or (pr.get("base") or {}).get("ref") != facts["base"]:
            why = "the pull request changed"
        elif reviews["change_requests"] or codex.get("id") != checked_codex.get("id") \
                or codex.get("state") != "APPROVED" or codex.get("commit") != facts["head"]:
            why = "its reviews changed"
    if why:
        return {"ok": False, "error": f"not queued: {why} during the check; run preflight again"}
    try:
        data = graphql_data(gh.graphql(ENQUEUE_MUTATION, {"id": facts["node_id"], "head": facts["head"]},
                                       attempts=1), "enqueuePullRequest")
        entry = (data.get("enqueuePullRequest") or {}).get("mergeQueueEntry")
        if entry and entry.get("position"):
            return {"ok": True, "position": entry["position"], "state": entry.get("state")}
        problem = "the request returned no queue entry"
    except (Failure, ValueError, OSError, http.client.HTTPException) as error:
        problem = str(error) or type(error).__name__
    # The outcome is unknown: read the entry back, and never send the request a second time.
    queue = get_queue(gh, facts["base"], facts["pr"])
    mine = next((e for e in queue["entries"] if e["number"] == facts["pr"]), None)
    if queue["own"] and mine and mine["head"] == facts["head"]:
        return {"ok": True, "position": queue["own"].get("position"), "state": queue["own"].get("state"),
                "note": f"queued with head {short(facts['head'])}, although {problem}"}
    return {"ok": False, "error": f"{problem}; it is not queued with head {short(facts['head'])}"}


def render(result: dict) -> str:
    """The verdict as text. Every value is passed through `shown`: file names and messages come from the
    pull requests and GitHub, and must not be able to forge a line or steer the terminal."""
    lines = [f"#{result['pr']} {shown(short(result['head']))}: {result['verdict']}"]
    for c in result["checks"]:
        lines.append(f"  {'ok  ' if c['ok'] else 'FAIL'}  {c['name']}: {shown(c['detail'])}")
        lines.extend(f"          - {shown(item)}" for item in c["items"])
        if c["next"]:
            lines.append(f"          -> {shown(c['next'])}")
    lines.extend(f"  warn  {shown(warning)}" for warning in result["warnings"])
    if result.get("next"):
        lines.append(f"Next: {shown(result['next'])}")
    queued = result.get("enqueue")
    if queued and queued["ok"]:
        lines.append(f"Queued at position {shown(queued['position'])} ({shown(queued['state'])})"
                     + (f"; {shown(queued['note'])}" if queued.get("note") else ""))
    elif queued:
        lines.append(f"Enqueue: {shown(queued['error'])}")
    return "\n".join(lines)


def default_git_dir() -> Path:
    cache = os.environ.get("XDG_CACHE_HOME") or str(Path.home() / ".cache")
    return Path(cache) / "atlas-lean-preflight" / "repo.git"


def main(argv: list[str] | None = None, now: dt.datetime | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("pr", type=int, help="pull request number")
    parser.add_argument("--json", action="store_true", help="print the verdict and the facts as JSON")
    parser.add_argument("--enqueue", action="store_true", help="queue the pull request if it is READY")
    parser.add_argument("--max-age-hours", type=float, default=DEFAULT_MAX_AGE_HOURS,
                        help="oldest acceptable CI run on the head (default %(default)s)")
    parser.add_argument("--max-files", type=int, default=DEFAULT_MAX_FILES,
                        help="changed files above which to warn (default %(default)s)")
    parser.add_argument("--git-dir", type=Path, default=None,
                        help="the clone to work in (default $XDG_CACHE_HOME/atlas-lean-preflight/repo.git)")
    args = parser.parse_args(argv)
    if not math.isfinite(args.max_age_hours) or args.max_age_hours <= 0 or args.max_files <= 0:
        parser.error("--max-age-hours and --max-files must be positive and finite")
    if args.enqueue and args.max_age_hours > DEFAULT_MAX_AGE_HOURS:
        parser.error(f"--enqueue checks freshness at {DEFAULT_MAX_AGE_HOURS:g} hours or less")
    token = read_token()
    if not token:
        print("preflight: no GitHub token; set GH_TOKEN or log in with `gh auth login`", file=sys.stderr)
        return 2
    gh = GitHub(token)
    git = Git(args.git_dir or default_git_dir(), f"https://github.com/{REPO}.git")
    try:
        with git.locked():
            facts = gather(gh, git, args.pr, now)
            result = evaluate(facts, now or dt.datetime.now(dt.timezone.utc), args.max_age_hours, args.max_files)
            if args.enqueue:
                result["enqueue"] = enqueue(gh, result)
    except (Failure, OSError, ValueError, subprocess.SubprocessError, http.client.HTTPException) as error:
        print(f"preflight: {shown(error or type(error).__name__)}", file=sys.stderr)
        return 2
    result["api_calls"] = gh.calls
    print(json.dumps(result, indent=1) if args.json else render(result))
    if not result["ready"]:
        return 1
    return 0 if not args.enqueue or result["enqueue"]["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
