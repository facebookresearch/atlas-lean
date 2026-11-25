#!/usr/bin/env python3
"""Re-run a merge group's failed required checks once when they failed transiently.

`.github/workflows/merge-queue-retry.yml` runs this script when a merge-group
run of a workflow that reports a required check fails; its header states the
rule. In short:

* Only the pull request's current merge group counts: the pull request must
  still be in the queue, and its entry's head commit is the commit checked.
* The required checks are the check runs, on that commit, of the checks
  main's branch rules require (by name and app, from every page of the
  rules; with more pages than are read, one check required from different
  apps, or a check the repository declares required missing from them,
  nothing is decided), whether or not the rest of their workflow has
  finished. A check with more than one check run there is
  ambiguous, and nothing is re-run. A check fails when it completes with a
  conclusion other than success, neutral or skipped.
* A failed required check is *transient* only on a short allowlist: the job
  failed and its failed step's own output has one of the exact lines seen
  when the guard's reads of GitHub's API failed (a truncated answer, an HTML
  page, a server error), or the runner or GitHub reported losing the job
  while the step shows no exit of its own; and the step shows no failure of
  the tree's own checks. Anything else is unknown: a cancelled job without
  the runner's report (who cancelled is not visible), a job with more than
  one failed step, whose failed step's output cannot be read whole, whose
  log cannot be fetched, that timed out or that an annotation says ran too
  long or was cancelled on request, and every other message.
  When every failed required check of the merge group is transient, each
  completed run holding one has its failed jobs re-run once (attempt 1
  only), in active mode only, each after the required checks, the run and
  the queue entry have been read again and still support the decision.
* Every other failure is left to the queue. For a *deterministic* failure the
  report states, without acting, whether the pull request would be removed
  early: the grouping is ALLGREEN, the pull request is not at the front, and
  the entry ahead of it passed every required check.

The script only calls GitHub's REST and GraphQL APIs; it never checks out or
runs anything from the merge group. Its only write is the re-run request.
Every answer the rule depends on is checked for shape: a missing, malformed
or unidentifiable rule, page, check run, commit status, job, step or
annotation makes the decision unknown, and nothing is re-run; so does a
commit status reporting a required check, since only check runs are
classified, and a name that differs from a required check's only in case or
spacing.
Untrusted text (names, log lines) goes only to the job summary, as inert
Markdown, never to the job's output, where the runner would parse commands.

    retry.py --pr N

It reads GH_TOKEN, GITHUB_REPOSITORY, GITHUB_EVENT_NAME, GITHUB_EVENT_PATH,
GITHUB_API_URL, GITHUB_GRAPHQL_URL, GITHUB_SERVER_URL, GITHUB_STEP_SUMMARY and
MERGE_QUEUE_RETRY (`active` enables re-runs; anything else is a dry run).
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import http.client
import json
import os
import re
import secrets
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any, Iterable, Iterator

BASE_BRANCH = "main"
# A merge group's ref: gh-readonly-queue/<base branch>/pr-<number>-<base commit>.
QUEUE_BRANCH = re.compile(r"gh-readonly-queue/main/pr-([1-9][0-9]{0,6})-([0-9a-f]{40})")
SHA = re.compile(r"[0-9a-f]{40}")
PR_NUMBER = re.compile(r"[1-9][0-9]{0,6}")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}")
# The workflows that report main's required checks, by file and name. Only
# their merge-group runs are ever re-run.
WORKFLOWS = {
    ".github/workflows/ci.yml": "CI",
    ".github/workflows/source-diagnostics.yml": "Source diagnostics",
    ".github/workflows/bump-guard.yml": "Bump guard",
}
GITHUB_ACTIONS_APP = 15368  # the app that reports Actions jobs as check runs
FAILED = ("failure", "timed_out", "cancelled")  # what a job can fail with
PASSING = ("success", "neutral", "skipped")  # what satisfies a required check
TRANSIENT, DETERMINISTIC, UNKNOWN = "transient", "deterministic", "unknown"
LOG_LIMIT = 64 * 1024 * 1024  # bytes of a job log read at most
LINE_LIMIT = 64 * 1024  # bytes of one log line read at once
PAGES = 5  # pages of check runs read at most
ANNOTATION_PAGES = 4  # pages of a check run's annotations read at most
RULE_PAGES = 3  # pages of main's branch rules read at most
# The checks this repository declares required (scripts/test_merge_queue_checks.py
# and CONTRIBUTING.md); a test keeps the two lists equal. Main's rules must
# require each of them, or nothing is decided: a requirement this job cannot
# read (classic branch protection needs administration access) could hide one.
DECLARED = ("repository integrity", "build", "check the graph", "source-diagnostics", "guard")

# A Lean error, a FAIL line from the repository checks (scripts/check.sh), a
# declaration collision, a failed unit test, a module the build did not
# produce, a failed Lake target, and any line that starts with "error" (Lean
# and Lake also report errors without a location): failures of the tree's
# own checks, whatever words their messages contain. Most telling first.
CHECK_FAILURE = [re.compile(p) for p in (
    r"^error: \S+?\.lean:\d+:\d+:",
    r"\.lean:\d+:\d+: error\b",
    r"^FAIL \[[^\]]+\]:",
    r" is declared in both ",
    r"^FAIL: \S",
    r"^ERROR: \S+ \(",
    r"^FAILED \((?:failures|errors)=",
    r"^Missing compiled module: ",
    r"^\u2716 \[\d+/\d+\] ",
    r"^\s*(?:error|Error|ERROR)\b",  # an error without a location ("error: build failed")
)]
# A tool's own verdict ("guard: FAIL - ..."): a check failure.
TOOL_FAILURE = re.compile(r"^[\w.-]+: FAIL\b")
# Infrastructure failures: a short allowlist of the exact lines seen when a
# required check failed for no fault of the tree (the guard's reads of
# GitHub's API on 23 November 2026), each matched as a whole line. A missed
# re-run costs nothing beyond the queue's own behaviour; a wrong one costs a
# build, so nothing broader is matched.
INFRASTRUCTURE = [re.compile(p) for p in (
    r"^unexpected end of JSON input$",  # a truncated answer (gh)
    r"^invalid character '<' looking for beginning of value$",  # an HTML page (gh)
    r"^RuntimeError: gh api \S+ failed: gh: HTTP 5\d\d$",  # a server error (the guard's client)
)]
# The runner's annotations about losing a job, and GitHub's about failing to
# run it. A step can write an annotation with the same text, so one counts
# only if the failed step's output was read whole and shows no exit of its
# own ("Process completed with exit code").
RUNNER = [re.compile(p) for p in (
    r"^The runner has received a shutdown signal",
    r"^The (?:self-)?hosted runner: .* lost communication with the server",
    r"^GitHub Actions has encountered an internal error when running your job",
)]
EXITED = re.compile(r"^##\[error\]Process completed with exit code \d+\.$")
# A job or step stopped for running too long (the stop is the job's own), or
# a cancellation someone asked for: a person, or a newer run of the same
# concurrency group. A re-run would repeat it or go against it.
STOPPED = re.compile(r"has exceeded the maximum execution time|has timed out"
                     r"|\bwas cancell?ed by @|Canceling since a higher priority waiting request")
BIDI = set("\u200e\u200f\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069")
TIMESTAMP = re.compile(r"^\ufeff?(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2})(?:\.\d+)?Z ?")
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
INCOMPLETE = object()  # yielded in place of the rest of a log cut short
UNAVAILABLE = object()  # yielded in place of a log that could not be fetched at all


class LongLine(str):
    """The start of a log line longer than LINE_LIMIT, whose rest was not read."""


class GitHubError(RuntimeError):
    def __init__(self, status: int, message: str):
        super().__init__(f"GitHub API error {status}: {message}")
        self.status = status


class _HttpsOnlyRedirect(urllib.request.HTTPRedirectHandler):
    """Follow redirects (the job-log download) only to https URLs."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).scheme != "https":
            raise GitHubError(code, "refusing a redirect to a non-https URL")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


class Api:
    """GitHub's REST and GraphQL APIs with the job's token.

    The token is sent as an unredirected header, so the redirect of a log
    download to its storage URL does not carry it.
    """

    def __init__(self, token: str, api_url: str = "https://api.github.com",
                 graphql_url: str | None = None, attempts: int = 3):
        self.token = token
        self.api_url = api_url.rstrip("/")
        self.graphql_url = graphql_url or self.api_url + "/graphql"
        self.attempts = attempts
        self.opener = urllib.request.build_opener(_HttpsOnlyRedirect)

    def _open(self, method: str, url: str, body: Any = None, retry: bool = True):
        """The response (an HTTPError for 4xx and final 5xx answers).

        Reads are retried on server and network errors; a write is not, so
        that it is never sent twice.
        """
        data = None if body is None else json.dumps(body).encode()
        attempts = self.attempts if retry else 1
        for attempt in range(1, attempts + 1):
            request = urllib.request.Request(url, data=data, method=method)
            request.add_unredirected_header("Authorization", f"Bearer {self.token}")
            request.add_unredirected_header("Accept", "application/vnd.github+json")
            request.add_unredirected_header("X-GitHub-Api-Version", "2022-11-28")
            if data is not None:
                request.add_unredirected_header("Content-Type", "application/json")
            try:
                return self.opener.open(request, timeout=60)
            except urllib.error.HTTPError as error:
                if error.code < 500 or attempt == attempts:
                    return error
                error.close()
            except (urllib.error.URLError, OSError, http.client.HTTPException):
                if attempt == attempts:
                    raise
            time.sleep(2 * attempt)
        raise AssertionError("unreachable")

    def request(self, method: str, path: str, body: Any = None) -> tuple[int, Any]:
        response = self._open(method, self.api_url + path, body, retry=method == "GET")
        with response:
            raw = response.read()
            status = response.code
        try:
            return status, json.loads(raw) if raw else None
        except ValueError:
            return status, raw.decode("utf-8", "replace")[:500]

    def get(self, path: str) -> Any:
        status, data = self.request("GET", path)
        if status != 200:
            raise GitHubError(status, f"GET {path}")
        return data

    def post(self, path: str) -> int:
        status, _ = self.request("POST", path, {})
        if status >= 300:
            raise GitHubError(status, f"POST {path}")
        return status

    def graphql(self, query: str, variables: dict[str, Any]) -> Any:
        response = self._open("POST", self.graphql_url, {"query": query, "variables": variables})
        with response:
            raw = response.read()
            status = response.code
        try:
            payload = json.loads(raw) if raw else {}
        except ValueError:
            payload = {}
        if status != 200 or payload.get("errors") or "data" not in payload:
            raise GitHubError(status, "GraphQL query failed")
        return payload["data"]

    def job_log(self, repo: str, job_id: int) -> Iterator[Any]:
        """The job's log lines, then INCOMPLETE if it was cut short.

        UNAVAILABLE alone if the log could not be fetched at all.
        """
        try:
            response = self._open("GET", f"{self.api_url}/repos/{repo}/actions/jobs/{job_id}/logs")
        except (urllib.error.URLError, OSError, http.client.HTTPException, GitHubError):
            yield UNAVAILABLE
            return
        with response:
            if response.code != 200:
                yield UNAVAILABLE
                return
            headers = getattr(response, "headers", None)
            length = (headers.get("Content-Length") or "").strip() if headers else ""
            expected = int(length) if length.isdigit() else None
            read = 0
            try:
                while True:
                    raw = response.readline(LINE_LIMIT)
                    if not raw:
                        if expected is not None and read != expected:
                            yield INCOMPLETE  # the connection ended early
                        return
                    read += len(raw)
                    if read > LOG_LIMIT:
                        yield INCOMPLETE
                        return
                    line = raw.decode("utf-8", "replace")
                    if len(raw) == LINE_LIMIT and not raw.endswith(b"\n"):
                        # An oversized line: keep its start, for its timestamp,
                        # as a LongLine that no pattern is matched against, and
                        # skip the rest.
                        line = LongLine(line)
                        while True:
                            more = response.readline(LINE_LIMIT)
                            read += len(more)
                            if read > LOG_LIMIT:
                                yield INCOMPLETE
                                return
                            if not more or more.endswith(b"\n"):
                                break
                    yield line
            except (OSError, http.client.HTTPException, ValueError):
                yield INCOMPLETE


@dataclasses.dataclass
class Trigger:
    workflow: str
    run_id: int
    run_attempt: int
    conclusion: str
    pr: int
    base: str
    head_sha: str


@dataclasses.dataclass
class Entry:
    position: int
    state: str
    head: str | None
    base: str | None


@dataclasses.dataclass
class Failure:
    check: str
    check_id: int
    kind: str
    evidence: str
    step: str | None = None
    workflow: str | None = None
    run_id: int | None = None
    run_attempt: int | None = None
    run_completed: bool = False


@dataclasses.dataclass
class Report:
    """The job summary (Markdown, may quote untrusted text) and the decision."""

    pr: int
    mode: str
    lines: list[str] = dataclasses.field(default_factory=list)
    failures: list[Failure] = dataclasses.field(default_factory=list)
    decision: str = "none"
    rerun: list[int] = dataclasses.field(default_factory=list)

    def say(self, markdown: str) -> None:
        self.lines.append(markdown)

    def log(self, message: str) -> None:
        """A line of the job's output: fixed text and validated numbers only."""
        print(message)


def integer(value: Any) -> bool:
    """Whether a JSON value is an integer: Python's bool, JSON's true/false, is not."""
    return type(value) is int


def fold(name: str) -> str:
    """A check's name as GitHub may match it: case and spacing aside."""
    return " ".join(name.split()).casefold()


def queue_branch(name: Any) -> tuple[int, str] | None:
    """(pull request, base commit) of a merge group's ref name, or None."""
    if not isinstance(name, str):
        return None
    match = QUEUE_BRANCH.fullmatch(name)
    return (int(match.group(1)), match.group(2)) if match else None


def text(value: Any, limit: int = 160) -> str:
    """Untrusted text (names, log lines) as one inert Markdown code span."""
    cleaned = "".join(" " if ord(c) < 32 or 127 <= ord(c) < 160 or c in BIDI else c
                      for c in str(value))
    cleaned = " ".join(cleaned.replace("`", "'").replace("|", "/").split())
    if len(cleaned) > limit:
        cleaned = cleaned[:limit - 1] + "\u2026"
    return f"`{cleaned}`" if cleaned else "`-`"


def short(sha: str | None) -> str:
    return sha[:10] if isinstance(sha, str) and SHA.fullmatch(sha) else "-"


def parse_time(value: Any) -> dt.datetime | None:
    if not isinstance(value, str):
        return None
    try:
        return dt.datetime.strptime(value[:19], "%Y-%m-%dT%H:%M:%S")
    except ValueError:
        return None


TERMINAL = ("success", "failure", "cancelled", "skipped", "timed_out", "neutral", "action_required")


def readable_step(step: Any) -> bool:
    """A completed step has a terminal conclusion; any other step has none yet."""
    if not isinstance(step, dict):
        return False
    if step.get("status") == "completed":
        return step.get("conclusion") in TERMINAL
    return step.get("status") in ("queued", "in_progress") and step.get("conclusion") is None


def failed_steps(steps: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    """The job's completed steps that did not pass (action_required included)."""
    return [step for step in steps
            if step.get("status") == "completed" and step.get("conclusion") not in PASSING]


def line_kind(line: str) -> str | None:
    """DETERMINISTIC, TRANSIENT or None for one output line."""
    if any(p.search(line) for p in CHECK_FAILURE):
        return DETERMINISTIC
    if any(p.search(line) for p in INFRASTRUCTURE):
        return TRANSIENT
    if TOOL_FAILURE.search(line):
        return DETERMINISTIC
    return None


def classify(job_conclusion: str, steps: Iterable[dict[str, Any]],
             annotations: Iterable[str], log_lines: Iterable[Any]) -> tuple[str, str | None, str]:
    """(kind, failed step, evidence) of one failed job.

    Only the failed step's output counts: the lines after its command block
    (the first "##[group]Run ..." at or after its start, up to "##[endgroup]",
    which is skipped) and up to its completion, by timestamp. Lines of the
    same second before that block belong to the previous step and are
    dropped; after a command block in the step's last second, which may be
    the next step's, only check failures count. If the block is not found,
    the log cannot vouch for an infrastructure failure. A check failure
    outweighs anything else. Otherwise the failure is unknown if the job
    timed out, or an annotation says it or a step ran too long or that it was
    cancelled on request (by a person, or by a newer run of its concurrency
    group), if more than one
    step failed, or if the step's output could not be read whole (a line too
    long, a log cut short). It is transient if the runner or GitHub reported
    losing the job while the step's output, found after its closed command
    block, shows no exit of its own, or, unless the job was cancelled (by
    whom is not visible here), if the step's output has one of the
    allowlisted lines.
    """
    steps = list(steps) if isinstance(steps, list) else None
    if steps is None or not all(readable_step(s) for s in steps):
        return UNKNOWN, None, "the job's steps cannot be read"
    failed = failed_steps(steps)
    step = failed[0] if failed else None
    name = step.get("name") if step else None
    if step is not None and step.get("conclusion") not in FAILED:
        return UNKNOWN, name, f"the failed step concluded {step.get('conclusion')}"
    started = parse_time(step.get("started_at")) if step else None
    completed = parse_time(step.get("completed_at")) if step else None
    if started is None or completed is None:
        return UNKNOWN, name, "the failed step's start or end is unknown"
    annotations = list(annotations)
    stopped = job_conclusion == "timed_out" or any(STOPPED.search(m) for m in annotations)
    annotated = next((m for m in annotations if any(p.search(m) for p in RUNNER)), None)
    infrastructure = deterministic = None
    rank = len(CHECK_FAILURE) + 1
    header = None  # the step's command block: None before it, True inside, False after
    tail = False  # past a command block in the step's last second: maybe the next step's
    partial = False  # a line of the step's output was too long to read whole
    exited = False  # the step ended on its own, with an exit code
    stamp = None
    for raw in log_lines:
        if raw is UNAVAILABLE:
            # No output to weigh, nor any proof of how the step ended: only
            # the job's own conclusion counts.
            if len(failed) > 1:
                return UNKNOWN, name, "more than one step failed"
            if stopped:
                return UNKNOWN, name, "the job ran too long or was cancelled on request"
            return UNKNOWN, name, "the job's log could not be fetched"
        if raw is INCOMPLETE:
            if deterministic is not None:
                return DETERMINISTIC, name, deterministic
            return UNKNOWN, name, "the step's log could not be read whole"
        match = TIMESTAMP.match(raw)
        if match:
            stamp = parse_time(match.group(1))
            line = raw[match.end():]
        else:
            line = raw.lstrip("\ufeff")
        if started is not None and (stamp is None or stamp < started):
            continue
        if completed is not None and stamp is not None and stamp > completed:
            break
        line = ANSI.sub("", line).rstrip("\r\n")
        if line.startswith("##[group]Run "):
            if header is None:
                infrastructure = deterministic = None  # the previous step's last second
                rank = len(CHECK_FAILURE) + 1
                exited = False
                header = True
                continue
            if completed is not None and stamp is not None and stamp >= completed:
                # Within the step's last second this may be the next step's
                # command block, or the step's own output: from here on, a
                # check failure still counts, an infrastructure failure not.
                tail = True
        if header:
            header = not line.startswith("##[endgroup]")
            continue
        if isinstance(raw, LongLine):
            partial = True
            continue
        if EXITED.match(line):
            exited = True  # in the ambiguous tail too: it vetoes a lost runner
            continue
        kind = line_kind(line)
        if kind == TRANSIENT:
            if not tail:
                infrastructure = infrastructure or line
        elif kind == DETERMINISTIC:
            index = next((i for i, p in enumerate(CHECK_FAILURE) if p.search(line)),
                         len(CHECK_FAILURE))
            if index < rank:
                deterministic, rank = line, index
    if header is None:
        infrastructure = None  # no step boundary: the log cannot vouch for a retry
    if deterministic is not None:
        return DETERMINISTIC, name, deterministic
    if stopped:
        return UNKNOWN, name, "the job ran too long or was cancelled on request"
    if len(failed) > 1:
        return UNKNOWN, name, "more than one step failed"
    if partial:
        return UNKNOWN, name, "a line of the step's output was too long to read whole"
    # A runner's message about losing the job counts only if the failed step's
    # command block was found and closed, and its output shows no exit.
    lost = annotated if annotated is not None and header is False and not exited else None
    if job_conclusion == "cancelled":
        # Who cancelled is not visible here (a person, a newer run of the
        # concurrency group, the runner): only the runner's or GitHub's own
        # report of losing the job counts.
        evidence = lost
    else:
        evidence = infrastructure or lost
    if evidence is not None:
        return TRANSIENT, name, evidence
    return UNKNOWN, name, "no infrastructure failure and no recognised check failure"


def read_trigger(event: dict[str, Any], repo: str) -> Trigger:
    """The failed merge-group run that triggered this job, validated."""
    run = event.get("workflow_run") or {}
    branch = queue_branch(run.get("head_branch"))
    problems = []
    if run.get("event") != "merge_group":
        problems.append("not a merge-group run")
    if WORKFLOWS.get(run.get("path")) != run.get("name"):
        problems.append("not a required-check workflow")
    if branch is None:
        problems.append("not a merge group of main")
    if not isinstance(run.get("head_sha"), str) or not SHA.fullmatch(run["head_sha"]):
        problems.append("invalid head commit")
    for key in ("repository", "head_repository"):
        if (run.get(key) or {}).get("full_name") != repo:
            problems.append(f"{key} is not this repository")
    if run.get("conclusion") not in FAILED:
        problems.append("the run did not fail")
    if not integer(run.get("id")) or not integer(run.get("run_attempt")):
        problems.append("invalid run id or attempt")
    if problems:
        raise ValueError("ignoring the triggering run: " + "; ".join(problems))
    return Trigger(run["name"], run["id"], run["run_attempt"], run["conclusion"],
                   branch[0], branch[1], run["head_sha"])


ENTRY_QUERY = """
query($owner: String!, $name: String!, $number: Int!, $base: String!) {
  repository(owner: $owner, name: $name) {
    ref(qualifiedName: $base) { target { oid } }
    pullRequest(number: $number) {
      state
      mergeQueueEntry { position state headCommit { oid } baseCommit { oid } }
    }
  }
}"""


def read_entry(api: Api, repo: str, pr: int) -> tuple[str | None, Entry | None]:
    """(main's commit, the pull request's queue entry or None)."""
    owner, name = repo.split("/")
    data = api.graphql(ENTRY_QUERY, {"owner": owner, "name": name, "number": pr,
                                     "base": f"refs/heads/{BASE_BRANCH}"})
    repository = data.get("repository") or {}
    main = ((repository.get("ref") or {}).get("target") or {}).get("oid")
    pull = repository.get("pullRequest") or {}
    entry = pull.get("mergeQueueEntry")
    if pull.get("state") != "OPEN" or not entry:
        return main, None
    return main, Entry(entry.get("position"), entry.get("state"),
                       (entry.get("headCommit") or {}).get("oid"),
                       (entry.get("baseCommit") or {}).get("oid"))


class Undecidable(Exception):
    """GitHub's answers cannot be read in a way that supports a decision.

    Raised for anything the rule depends on that is missing or malformed:
    main's rules, a page of check runs, a required check run. Triage then
    decides `unknown` and re-runs nothing.
    """


STATUSES = ("queued", "in_progress", "completed", "waiting", "requested", "pending")
STATES = ("error", "failure", "pending", "success")  # a commit status's states


def read_rules(api: Api, repo: str) -> tuple[str | None, dict[str, int | None]]:
    """(grouping strategy, required check name -> app id) of main's rules.

    Every page of the rules is read. Raises Undecidable if there are more
    pages than are read (a rule requiring another check could be among the
    rest), or if rules require one check from different apps: rulesets are
    layered, so every such requirement applies, and keeping one could hide a
    failure another sees.
    """
    rules: list[dict[str, Any]] = []
    for page in range(1, RULE_PAGES + 1):
        batch = api.get(f"/repos/{repo}/rules/branches/{BASE_BRANCH}"
                        f"?per_page=100&page={page}")
        if not isinstance(batch, list):
            raise GitHubError(200, "the branch rules are not a list")
        rules.extend(batch)
        if len(batch) < 100:
            break
    else:
        raise Undecidable(f"more rules apply to {BASE_BRANCH} than are read, so a required "
                          "check could be missed")
    strategy = None
    required: dict[str, int | None] = {}
    folded: dict[str, str] = {}
    for rule in rules:
        if not isinstance(rule, dict):
            raise Undecidable(f"a rule of {BASE_BRANCH} is unreadable")
        parameters = rule.get("parameters")
        if rule.get("type") == "merge_queue" and isinstance(parameters, dict):
            strategy = parameters.get("grouping_strategy")
        elif rule.get("type") == "required_status_checks":
            checks = (parameters.get("required_status_checks")
                      if isinstance(parameters, dict) else None)
            if not isinstance(checks, list):
                raise Undecidable("a rule requiring status checks does not list them")
            for check in checks:
                if not isinstance(check, dict) or not isinstance(check.get("context"), str):
                    raise Undecidable("a rule requires a status check that cannot be read")
                context, app = check["context"], check.get("integration_id")
                if folded.setdefault(fold(context), context) != context:
                    raise Undecidable(f"rules require {text(folded[fold(context)])} and "
                                      f"{text(context)}, which differ only in case or spacing")
                if app is not None and not integer(app):
                    raise Undecidable(f"a rule requires {text(context)} from an unreadable app")
                if context in required and required[context] != app:
                    raise Undecidable(f"rules require {text(context)} from different apps, "
                                      "and all of them apply")
                required[context] = app
    missing = [name for name in DECLARED if name not in required]
    if missing:
        raise Undecidable(f"{BASE_BRANCH}'s rules do not require "
                          f"{', '.join(text(name) for name in missing)}, which this "
                          "repository declares required")
    return strategy, required


def required_checks(api: Api, repo: str, sha: str,
                    required: dict[str, int | None]) -> dict[str, list[dict[str, Any]]]:
    """Every check run of each required check on a commit, newest first.

    A check run counts only if it comes from the app the rule names. A name
    with more than one check run is ambiguous: its newest run need not be
    the one the merge group's workflow reported.
    """
    found: list[dict[str, Any]] = []
    for page in range(1, PAGES + 1):
        data = api.get(f"/repos/{repo}/commits/{sha}/check-runs"
                       f"?filter=latest&per_page=100&page={page}")
        runs = data.get("check_runs") if isinstance(data, dict) else None
        if not isinstance(runs, list):
            raise Undecidable(f"a page of the check runs on {short(sha)} is unreadable")
        found.extend(runs)
        if len(runs) < 100:  # only a short, readable page ends the list
            break
    else:
        raise Undecidable(f"more than {PAGES * 100} check runs on {short(sha)}")
    candidates: dict[str, list[dict[str, Any]]] = {name: [] for name in required}
    folds = {fold(name): name for name in required}
    for check in found:
        # A check run that may be a required one but cannot be identified, or
        # whose state cannot be read, makes the whole answer unreadable.
        if not isinstance(check, dict) or not isinstance(check.get("name"), str):
            raise Undecidable(f"a check run on {short(sha)} has no readable name")
        name = check["name"]
        if name not in required:
            if fold(name) in folds:
                raise Undecidable(f"a check run named {text(name)} differs from the required "
                                  f"{text(folds[fold(name)])} only in case or spacing")
            continue
        if required[name] is not None:
            app = check.get("app")
            app = app.get("id") if isinstance(app, dict) else None
            if not integer(app):
                raise Undecidable(f"a check run of {text(name)} has no readable app")
            if app != required[name]:
                continue  # another app's check run of the same name
        status, conclusion = check.get("status"), check.get("conclusion")
        if (not integer(check.get("id")) or status not in STATUSES
                or (status == "completed") != isinstance(conclusion, str)
                or not (conclusion is None or isinstance(conclusion, str))):
            raise Undecidable(f"a check run of {text(name)} cannot be identified or read")
        candidates[name].append(check)
    required_statuses(api, repo, sha, required)
    for checks in candidates.values():
        checks.sort(key=lambda check: check["id"], reverse=True)
    return candidates


def required_statuses(api: Api, repo: str, sha: str, required: dict[str, int | None]) -> None:
    """Raise Undecidable if a commit status reports a required check on a commit.

    A rule may accept a commit status for a required check, and this job
    classifies check runs only, so such a check is left to the queue.
    """
    for page in range(1, PAGES + 1):
        data = api.get(f"/repos/{repo}/commits/{sha}/status?per_page=100&page={page}")
        statuses = data.get("statuses") if isinstance(data, dict) else None
        if not isinstance(statuses, list) or not all(
                isinstance(status, dict) and isinstance(status.get("context"), str)
                and status.get("state") in STATES for status in statuses):
            raise Undecidable(f"the commit statuses on {short(sha)} are unreadable")
        folds = {fold(name) for name in required}
        reported = sorted({status["context"] for status in statuses
                           if fold(status["context"]) in folds})
        if reported:
            raise Undecidable(f"a commit status reports {', '.join(text(n) for n in reported)} "
                              f"on {short(sha)}, and this job reads check runs only")
        if len(statuses) < 100:
            return
    raise Undecidable(f"more than {PAGES * 100} commit statuses on {short(sha)}")


def snapshot(checks: dict[str, list[dict[str, Any]]]) -> dict[str, list[tuple]]:
    """What the decision rests on: each candidate's id, status and conclusion."""
    return {name: [(c["id"], c.get("status"), c.get("conclusion")) for c in candidates]
            for name, candidates in checks.items()}


def failing(check: dict[str, Any]) -> bool:
    return check.get("status") == "completed" and check.get("conclusion") not in PASSING


def explain(api: Api, repo: str, pr: int, entry: Entry, check: dict[str, Any],
            runs: dict[int, dict[str, Any]]) -> Failure:
    """Classify one failed required check run of the merge group."""
    failure = Failure(check["name"], check["id"], UNKNOWN,
                      "not a job of a required-check workflow on this merge group")
    if check.get("conclusion") not in FAILED:
        failure.evidence = f"concluded {check.get('conclusion')}, which a re-run does not address"
        return failure
    app = check.get("app")
    if not isinstance(app, dict) or app.get("id") != GITHUB_ACTIONS_APP:
        return failure
    job = api.get(f"/repos/{repo}/actions/jobs/{check['id']}")  # a job's id is its check run's
    run_id = job.get("run_id")
    if not (integer(run_id) and job.get("head_sha") == entry.head
            and job.get("id") == check["id"] and job.get("name") == check["name"]
            and job.get("status") == "completed" and integer(job.get("run_attempt"))):
        return failure
    if run_id not in runs:
        runs[run_id] = api.get(f"/repos/{repo}/actions/runs/{run_id}")
    run = runs[run_id]
    branch = f"gh-readonly-queue/{BASE_BRANCH}/pr-{pr}-{entry.base}"
    if not (run.get("path") in WORKFLOWS and WORKFLOWS[run["path"]] == run.get("name")
            and run.get("event") == "merge_group" and run.get("head_sha") == entry.head
            and run.get("head_branch") == branch and run.get("id") == run_id
            and (run.get("head_repository") or {}).get("full_name") == repo
            and job.get("run_attempt") == run.get("run_attempt")
            and integer(run.get("run_attempt"))
            and job.get("conclusion") == check.get("conclusion")):
        return failure
    annotations: list[str] = []
    for page in range(1, ANNOTATION_PAGES + 1):
        batch = api.get(f"/repos/{repo}/check-runs/{check['id']}/annotations"
                        f"?per_page=50&page={page}")
        if not isinstance(batch, list) or not all(
                isinstance(a, dict) and isinstance(a.get("message"), str) for a in batch):
            return Failure(check["name"], check["id"], UNKNOWN, "unreadable annotations",
                           None, run["name"], run_id, run["run_attempt"],
                           run.get("status") == "completed")
        annotations.extend(a["message"] for a in batch)
        if len(batch) < 50:
            break
    else:
        # The rule needs every annotation (one may say the job ran too long).
        return Failure(check["name"], check["id"], UNKNOWN, "too many annotations to read",
                       None, run["name"], run_id, run["run_attempt"],
                       run.get("status") == "completed")
    kind, step, evidence = classify(check["conclusion"], job.get("steps"), annotations,
                                    api.job_log(repo, check["id"]))
    return Failure(check["name"], check["id"], kind, evidence, step, run["name"], run_id,
                   run["run_attempt"], run.get("status") == "completed")


def triage(api: Api, repo: str, pr: int, mode: str, trigger: Trigger | None = None,
           report: Report | None = None, server: str = "https://github.com") -> Report:
    """Check the pull request's current merge group; re-run or record as the rule says."""
    report = report or Report(pr, mode)
    report.say(f"### Merge queue retry: #{pr}")
    report.say(f"- Mode: **{mode}**" + ("" if mode == "active" else
               " (nothing is re-run; re-runs need the repository variable "
               "`MERGE_QUEUE_RETRY` set to `active`)"))
    report.log(f"Merge queue retry for #{pr}, mode {mode}.")
    if trigger is not None:
        report.say(f"- Trigger: {text(trigger.workflow)} run {trigger.run_id} attempt "
                   f"{trigger.run_attempt} ({trigger.conclusion}) on merge group "
                   f"{short(trigger.head_sha)} (base {short(trigger.base)})")
        report.log(f"Triggered by run {trigger.run_id} attempt {trigger.run_attempt}.")
    try:
        strategy, required = read_rules(api, repo)
    except Undecidable as reason:
        return decide(report, "unknown", f"{reason}; left to the queue.")
    main, entry = read_entry(api, repo, pr)
    if not required:
        return decide(report, "none", f"no required checks on {BASE_BRANCH}; nothing to do.")
    if entry is None:
        return decide(report, "none", "the pull request is not in the merge queue; nothing to do.")
    if not all(isinstance(sha, str) and SHA.fullmatch(sha) for sha in (entry.head, entry.base)):
        return decide(report, "none", "the queue entry has no merge group; nothing to do.")
    report.say(f"- Queue: position {entry.position}, merge group {short(entry.head)} on "
               f"{short(entry.base)}; {BASE_BRANCH} at {short(main)}; grouping {text(strategy)}")
    position = entry.position if integer(entry.position) else "-"
    report.log(f"Queue position {position}, merge group {short(entry.head)}.")
    if trigger is not None and trigger.head_sha != entry.head:
        report.say("- The triggering run belongs to an older merge group, which is never acted "
                   "on; checked the current merge group instead.")
    try:
        checks = required_checks(api, repo, entry.head, required)
    except Undecidable as reason:
        return decide(report, "unknown", f"{reason}; left to the queue.")
    ambiguous = [name for name, candidates in checks.items() if len(candidates) > 1]
    if ambiguous:
        names = ", ".join(text(name) for name in ambiguous)
        return decide(report, "ambiguous", f"more than one check run reports {names} on the "
                                           "merge group's commit; left to the queue.")
    runs: dict[int, dict[str, Any]] = {}
    for candidates in checks.values():
        if candidates and failing(candidates[0]):
            report.failures.append(explain(api, repo, pr, entry, candidates[0], runs))
    if report.failures:
        report.say("")
        report.say("| Check | Workflow run | Step | Class | Evidence |")
        report.say("| --- | --- | --- | --- | --- |")
        for failure in report.failures:
            run = "-"
            if failure.run_id is not None:
                log = f"{server}/{repo}/actions/runs/{failure.run_id}/job/{failure.check_id}"
                run = (f"{text(failure.workflow)} [{failure.run_id}]({log}) "
                       f"attempt {failure.run_attempt}")
            report.say(f"| {text(failure.check)} | {run} | {text(failure.step)} | {failure.kind} "
                       f"| {text(failure.evidence)} |")
            report.log(f"Failed required check run {failure.check_id}: {failure.kind}.")
        report.say("")
    if not report.failures:
        pending = [name for name, candidates in checks.items()
                   if not candidates or candidates[0].get("status") != "completed"]
        state = "other required checks are still running" if pending else "nothing to re-run"
        return decide(report, "none",
                      f"no failed required check on the current merge group; {state}.")
    kinds = {failure.kind for failure in report.failures}
    if DETERMINISTIC in kinds:
        observe(api, repo, pr, report, strategy, required, main, entry)
    elif kinds == {TRANSIENT}:
        rerun(api, repo, pr, report, entry, required, snapshot(checks))
    else:
        decide(report, "unknown", "a failed required check shows neither an infrastructure "
                                  "failure nor a recognised check failure; left to the queue.")
    return report


def decide(report: Report, decision: str, markdown: str) -> Report:
    report.decision = decision
    report.say(f"- Decision: {markdown}")
    report.log(f"Decision: {decision}.")
    return report


def observe(api: Api, repo: str, pr: int, report: Report, strategy: str | None,
            required: dict[str, int | None], main: str | None, entry: Entry) -> None:
    """Record, without acting, whether the pull request would be removed early."""
    culprit = next(f for f in report.failures if f.kind == DETERMINISTIC)
    where = f"{text(culprit.check)} ({text(culprit.workflow)}: {text(culprit.step)})"
    if strategy != "ALLGREEN":
        decide(report, "observe", f"observe only. Grouping is {text(strategy)}; the "
                                  "early-removal rule is defined for ALLGREEN only, so no "
                                  "decision. Left to the queue.")
    elif entry.base == main or (integer(entry.position) and entry.position == 1):
        decide(report, "observe", f"observe only. #{pr} is at the front of the queue, which "
                                  f"removes it itself; {where} failed.")
    else:
        try:
            ahead = required_checks(api, repo, entry.base, required)
        except Undecidable as reason:
            decide(report, "observe", f"observe only. Not attributable: {reason}.")
            return
        missing = [f"{text(name)} {text(state(candidates))}" for name, candidates in ahead.items()
                   if len(candidates) != 1 or candidates[0].get("conclusion") not in PASSING]
        if missing:
            decide(report, "observe", "observe only. Not attributable yet: the entry ahead has "
                                      "not passed every required check "
                                      f"({', '.join(missing)}); the queue removes #{pr} once the "
                                      "entries ahead of it merge.")
        else:
            decide(report, "would-dequeue", f"observe only. **Would dequeue #{pr}**: {where} "
                                            "failed while the entry ahead passed every required "
                                            "check. Nothing was removed.")


def state(candidates: list[dict[str, Any]]) -> str:
    """A required check's state: its run's conclusion, else its status."""
    if not candidates:
        return "missing"
    if len(candidates) > 1:
        return "ambiguous"
    return candidates[0].get("conclusion") or candidates[0].get("status") or "missing"


def rerun(api: Api, repo: str, pr: int, report: Report, entry: Entry,
          required: dict[str, int | None], seen: dict[str, list[tuple]]) -> None:
    """Re-run, once, the failed jobs of each completed run with a transient failure."""
    runs: dict[int, Failure] = {}
    checks_of: dict[int, set[str]] = {}
    for failure in report.failures:
        runs.setdefault(failure.run_id, failure)
        checks_of.setdefault(failure.run_id, set()).add(failure.check)
    report.decision = "retry"
    eligible = []
    for run_id, failure in runs.items():
        label = f"{text(failure.workflow)} run {run_id}"
        if not failure.run_completed:
            report.say(f"- Decision: {label} is still running; its completion is checked again.")
            report.log(f"Run {run_id} is still running.")
        elif failure.run_attempt != 1:
            report.say(f"- Decision: {label} was already re-run (attempt {failure.run_attempt}); "
                       "left to the queue.")
            report.log(f"Run {run_id} is on attempt {failure.run_attempt}: not re-run.")
        elif report.mode != "active":
            report.say(f"- Decision: would re-run the failed jobs of {label} (dry run).")
            report.log(f"Would re-run the failed jobs of run {run_id} (dry run).")
        else:
            eligible.append((run_id, label))
    restarted: set[str] = set()  # checks whose jobs this job asked to re-run
    submitted: set[int] = set()  # runs this job asked to re-run
    unsent: list[int] = []
    for run_id, label in eligible:
        # Things may have moved since the first reads. Before each request,
        # read main's rules (the same checks still required, from the same
        # apps), the required checks (nothing changed but what this job's own
        # earlier requests restarted), then the run, then the queue entry last,
        # and stop unless all still match. GitHub offers no conditional
        # re-run, so a change in the moment between the last read and the
        # request can still re-run a stale group's jobs; that costs a build and
        # changes nothing in the queue.
        try:
            _, now_required = read_rules(api, repo)
        except Undecidable:
            now_required = None
        if now_required != required:
            report.say("- Decision: the checks main's rules require changed while checking; "
                       f"{label} not re-run (the next completion is checked again).")
            report.log(f"The required checks' rules changed: run {run_id} not re-run.")
            break
        try:
            now_checks = snapshot(required_checks(api, repo, entry.head, required))
        except Undecidable:
            now_checks = None
        successors = {name: verified_successors(api, repo, entry, name, seen.get(name, []),
                                                now_checks.get(name, []), submitted)
                      for name in restarted} if now_checks is not None else {}
        if now_checks is None or not settled(seen, now_checks, successors):
            report.say("- Decision: the merge group's required checks changed while checking; "
                       f"{label} not re-run (the next completion is checked again).")
            report.log(f"The required checks changed: run {run_id} not re-run.")
            break
        current = api.get(f"/repos/{repo}/actions/runs/{run_id}")
        attempt = current.get("run_attempt")
        if (current.get("status") != "completed" or not integer(attempt) or attempt != 1
                or current.get("head_sha") != entry.head):
            report.say(f"- Decision: {label} is no longer a completed first attempt; not re-run.")
            report.log(f"Run {run_id} changed: not re-run.")
            break
        _, now = read_entry(api, repo, pr)
        if now is None or now.head != entry.head:
            report.say(f"- Decision: the queue entry changed while checking; {label} not re-run, "
                       "as its merge group may be stale.")
            report.log(f"The queue entry changed: run {run_id} not re-run.")
            break
        # Recorded first: a request that fails may still have gone through.
        restarted |= checks_of[run_id]
        submitted.add(run_id)
        try:
            api.post(f"/repos/{repo}/actions/runs/{run_id}/rerun-failed-jobs")
        except (GitHubError, urllib.error.URLError, OSError, http.client.HTTPException) as error:
            # Not repeated; the other runs are still tried, and the job fails.
            unsent.append(run_id)
            report.say(f"- Decision: the request to re-run {label} failed ({text(error)}); "
                       "not repeated.")
            report.log(f"The request to re-run run {run_id} failed.")
            continue
        report.rerun.append(run_id)
        report.say(f"- Decision: re-ran the failed jobs of {label}.")
        report.log(f"Re-ran the failed jobs of run {run_id}.")
    if unsent:
        raise GitHubError(0, f"{len(unsent)} re-run request(s) failed")


def verified_successors(api: Api, repo: str, entry: Entry, name: str, before: list[tuple],
                        after: list[tuple], submitted: set[int]) -> set[int]:
    """The new check runs of a re-run check that are jobs of a later attempt of a run
    this job asked to re-run, on the merge group's commit."""
    known = {run[0] for run in before}
    found = set()
    for check_id, _, _ in after:
        if check_id in known:
            continue
        try:
            job = api.get(f"/repos/{repo}/actions/jobs/{check_id}")
        except GitHubError:
            continue
        attempt = job.get("run_attempt")
        if (job.get("run_id") in submitted and integer(attempt) and attempt > 1
                and job.get("head_sha") == entry.head and job.get("id") == check_id
                and job.get("name") == name):
            found.add(check_id)
    return found


def settled(seen: dict[str, list[tuple]], now: dict[str, list[tuple]],
            successors: dict[str, set[int]] | None = None) -> bool:
    """Whether the required checks still support the decision.

    Every check run seen is still the only one for its check, with the same
    status and conclusion, except that a pending one may have passed; a check
    that had no run may have gained one that has not failed. For a check whose
    job this job asked to re-run (a key of `successors`), the failed run may
    stay as it was, and at most one verified successor, which has not failed,
    may appear next to it or in its place; nothing else.
    """
    successors = successors or {}
    for name in seen.keys() | now.keys():
        before, after = seen.get(name, []), now.get(name, [])
        if name in successors:
            kept = [run for run in after if run in before]
            new = [run for run in after if run[0] in successors[name]]
            if (not after or len(kept) + len(new) != len(after) or len(kept) > 1
                    or len(new) > 1):
                return False
            if any(run[1] == "completed" and run[2] not in PASSING for run in new):
                return False
            continue
        if len(before) > 1 or len(after) > 1:
            return False
        if not before:
            if after and after[0][1] == "completed" and after[0][2] not in PASSING:
                return False
            continue
        if not after:
            return False
        old_id, old_status, old_conclusion = before[0]
        new_id, new_status, new_conclusion = after[0]
        if new_id != old_id:
            return False
        if old_status == "completed":
            if (new_status, new_conclusion) != (old_status, old_conclusion):
                return False
        elif new_status == "completed" and new_conclusion not in PASSING:
            return False
    return True


def main(argv: list[str] | None = None) -> int:
    # Nothing printed after this line is read as a workflow command.
    print(f"::stop-commands::{secrets.token_hex(16)}")
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--pr", required=True, help="number of the queued pull request")
    args = parser.parse_args(argv)
    if not PR_NUMBER.fullmatch(args.pr):
        parser.error("--pr must be a pull request number")
    pr = int(args.pr)
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if not REPOSITORY.fullmatch(repo):
        parser.error("GITHUB_REPOSITORY must be owner/name")
    trigger = None
    mode = "dry-run"
    if os.environ.get("GITHUB_EVENT_NAME") == "workflow_run":
        with open(os.environ["GITHUB_EVENT_PATH"], encoding="utf-8") as handle:
            event = json.load(handle)
        try:
            trigger = read_trigger(event, repo)
            if trigger.pr != pr:
                raise ValueError("ignoring the triggering run: it is for another pull request")
        except ValueError as error:
            write_summary([f"### Merge queue retry: #{pr}", f"- {text(error, 300)}"])
            print("Ignored an ineligible trigger.")
            return 0
        if os.environ.get("MERGE_QUEUE_RETRY") == "active":
            mode = "active"
    api = Api(os.environ["GH_TOKEN"], os.environ.get("GITHUB_API_URL", "https://api.github.com"),
              os.environ.get("GITHUB_GRAPHQL_URL"))
    report = Report(pr, mode)
    try:
        triage(api, repo, pr, mode, trigger, report,
               os.environ.get("GITHUB_SERVER_URL", "https://github.com"))
    except Exception as error:
        report.say(f"- Error, no further action: {text(error, 300)}")
        raise
    finally:
        write_summary(report.lines)
    return 0


def write_summary(lines: list[str]) -> None:
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
