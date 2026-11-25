#!/usr/bin/env python3
"""Tests for scripts/queue/retry.py and .github/workflows/merge-queue-retry.yml.

Offline: GitHub is replaced by recorded API responses and job logs from the
merge queue of 23 November 2026, in fixtures/retry/. api.json maps each
request the script makes to a trimmed copy of GitHub's answer, recorded the
same evening (fields the script does not read are left out; values are
unchanged). logs/ holds the failed jobs' logs, cut to the failed step and the
lines around it, with trailing whitespace removed. The queue entries no
longer exist, so the GraphQL answers are built here in GitHub's shape from
that day's queue events. A test that needs the state at the moment of a
failure, before later jobs finished, edits a copy of the recorded answer and
says so:

* #6624: `guard` failed on "unexpected end of JSON input" (18:32:14) while
  the PR's build was still running; the queue removed it at 18:57:03.
* #4431: `guard` read an HTML page instead of JSON (12:21:49).
* #6651: `guard` got an HTTP 503 (17:43:11); `repository integrity` then
  failed a test (17:43:45) and `build` failed on Lean errors (18:04:56),
  because the entry ahead broke.
* #6650: `build` failed on a declaration collision with #6645 (19:18:37).
* #6218: `build` failed on a Lean error after the Lean bump (17:33:16).

Run with: python3 -m unittest discover -s scripts/queue -p 'test_*.py'
"""

from __future__ import annotations

import ast
import contextlib
import copy
import io
import json
import os
import re
import tempfile
import unittest
import urllib.error
from pathlib import Path
from unittest import mock

import retry

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FIXTURES = HERE / "fixtures" / "retry"
WORKFLOW = ROOT / ".github" / "workflows" / "merge-queue-retry.yml"
REPO = "facebookresearch/atlas-lean"
API = f"/repos/{REPO}"
MAIN = "e2c150658f53b201225947e60b43a84f48bae826"  # a commit of main, not a group's base

# pr -> (merge group head, base commit, failed run, failed job)
GROUPS = {
    6624: ("98a4728fa5d2b367b9dfcc01f75fa9326286683b", "e6acc6d2dbed5de71d67fe25399bf7d652e9db0c",
           45239318416, 137919366370),
    4431: ("571944cf974ef17b4c36cc9c64184f7661c05336", "ec82ec8b7c8ef6a61d6debc1b2304bbee29a8795",
           45173480652, 137688648358),
    6651: ("1c3e7623ed3295e5ede7ed95f098637e162417a1", "71e3543604ee5b688eade7de381c4c44412216a5",
           45230586519, 137888725343),
    6650: ("62cb8d388ebb1ed29c24d73caeba42ef149bab5b", "22689f410cc74a533534ff68ddf5c72f5e2a19eb",
           45243956358, 137935699642),
    6218: ("f0d1e156198f7fc2dda05d0507957774f3835f70", "49fb838d2859c4cd95077ad36d5948a6a953b68b",
           45223093365, 137862285726),
}
RERUN = f"{API}/actions/runs/{{}}/rerun-failed-jobs"


def checks_path(sha: str) -> str:
    return f"{API}/commits/{sha}/check-runs?filter=latest&per_page=100&page=1"


class FakeApi:
    """The recorded GitHub API; records every call and refuses anything unrecorded."""

    def __init__(self, entries: dict, main: str = MAIN):
        self.responses = json.loads((FIXTURES / "api.json").read_text(encoding="utf-8"))
        self.entries = entries
        self.main = main
        self.calls: list[tuple[str, str]] = []
        self.before_get = None
        self.logs: dict[int, list] = {}

    def get(self, path: str):
        self.calls.append(("GET", path))
        if self.before_get:
            self.before_get(path)
        key = f"GET {path}"
        if key not in self.responses:
            raise AssertionError(f"unrecorded request: {key}")
        return copy.deepcopy(self.responses[key])

    def post(self, path: str) -> int:
        self.calls.append(("POST", path))
        return 201

    def graphql(self, query: str, variables: dict):
        self.calls.append(("GRAPHQL", query))
        assert "mutation" not in query, "the script must not send GraphQL mutations"
        assert variables["base"] == "refs/heads/main"
        entry = self.entries.get(variables["number"])
        return {"repository": {"ref": {"target": {"oid": self.main}},
                               "pullRequest": {"state": "OPEN", "mergeQueueEntry": entry}}}

    def job_log(self, repo: str, job_id: int):
        self.calls.append(("LOG", str(job_id)))
        assert repo == REPO
        if job_id in self.logs:
            yield from self.logs[job_id]
            return
        yield from (FIXTURES / "logs" / f"{job_id}.txt").read_text(encoding="utf-8").splitlines(True)

    def posts(self) -> list[str]:
        return [path for method, path in self.calls if method == "POST"]

    def check(self, sha: str, name: str, **fields) -> None:
        """Edit a recorded check run on a commit (the state before later jobs finished)."""
        for check in self.responses[f"GET {checks_path(sha)}"]["check_runs"]:
            if check["name"] == name:
                check.update(fields)

    def before_main_ran(self, sha: str) -> None:
        """A merged group's commit as it was before main's push run checked it again.

        The answers were recorded after the entries merged, when CI and Source
        diagnostics had also run on main for the same commit, adding a second
        check run, with a higher id, for each check. Keep each check's first.
        """
        data = self.responses[f"GET {checks_path(sha)}"]
        first: dict[str, int] = {}
        for check in data["check_runs"]:
            first[check["name"]] = min(check["id"], first.get(check["name"], check["id"]))
        data["check_runs"] = [c for c in data["check_runs"] if c["id"] == first[c["name"]]]
        data["total_count"] = len(data["check_runs"])


def entry(pr: int, position: int = 5, head: str | None = None, base: str | None = None) -> dict:
    group_head, group_base = GROUPS[pr][:2]
    return {"position": position, "state": "AWAITING_CHECKS",
            "headCommit": {"oid": head or group_head}, "baseCommit": {"oid": base or group_base}}


def trigger(pr: int, attempt: int = 1, head: str | None = None) -> retry.Trigger:
    group_head, group_base, run_id, _ = GROUPS[pr]
    return retry.Trigger("Bump guard", run_id, attempt, "failure", pr, group_base, head or group_head)


def quiet(function, *args, **kwargs):
    with contextlib.redirect_stdout(io.StringIO()):
        return function(*args, **kwargs)


def summary(report: retry.Report) -> str:
    return "\n".join(report.lines)


class Classify(unittest.TestCase):
    STEPS = [
        {"name": "Fetch Mathlib cache", "status": "completed", "conclusion": "success",
         "started_at": "2026-11-23T10:00:00Z", "completed_at": "2026-11-23T10:01:00Z"},
        {"name": "Build", "status": "completed", "conclusion": "failure",
         "started_at": "2026-11-23T10:01:00Z", "completed_at": "2026-11-23T10:05:00Z"},
        {"name": "Post", "status": "completed", "conclusion": "success",
         "started_at": "2026-11-23T10:05:00Z", "completed_at": "2026-11-23T10:06:00Z"},
    ]

    def log(self, *lines: tuple[str, str], header: bool = True) -> list[str]:
        start = [("10:01:00", "##[group]Run scripts/check.sh build"), ("10:01:00", "##[endgroup]")]
        return [f"2026-11-23T{time}.1234567Z {text}\n" for time, text in (start if header else []) + list(lines)]

    def kind(self, *lines: tuple[str, str], annotations=(), conclusion="failure") -> str:
        return retry.classify(conclusion, self.STEPS, list(annotations), self.log(*lines))[0]

    def recorded(self, pr: int, job_id: int | None = None):
        job_id = job_id or GROUPS[pr][3]
        job = json.loads((FIXTURES / "api.json").read_text(encoding="utf-8"))[f"GET {API}/actions/jobs/{job_id}"]
        log = (FIXTURES / "logs" / f"{job_id}.txt").read_text(encoding="utf-8").splitlines(True)
        return retry.classify(job["conclusion"], job["steps"], ["Process completed with exit code 1."], log)

    def test_recorded_guard_api_failures_are_transient(self):
        for pr, evidence in ((6624, "unexpected end of JSON input"),
                             (4431, "invalid character '<' looking for beginning of value"),
                             (6651, "gh: HTTP 503")):
            with self.subTest(pr=pr):
                kind, step, found = self.recorded(pr)
                self.assertEqual((kind, step), (retry.TRANSIENT, "Validate pin change against base"))
                self.assertIn(evidence, found)

    def test_recorded_check_failures_are_deterministic(self):
        for pr, job_id, step, evidence in (
                (6650, None, "Build extension libraries",
                 "FAIL [declaration collisions]: AlgebraicGeometry.ProjSpace.grad0Equiv"),
                (6218, None, "Build extension libraries",
                 "error: MathlibExt/Probability/DyadicTruncation.lean:183:45: Type mismatch"),
                (6651, 137888725562, "Build extension libraries", "error: MathlibExt/Probability/"),
                (6651, 137888725766, "Run deterministic repository checks", "FAIL: test_the_committed_weights")):
            with self.subTest(pr=pr, job=job_id):
                kind, found_step, found = self.recorded(pr, job_id)
                self.assertEqual((kind, found_step), (retry.DETERMINISTIC, step))
                self.assertTrue(found.startswith(evidence), found)

    def test_check_failures_win_whatever_their_message_says(self):
        for line in ("error: MathlibExt/Http.lean:12:3: expected HTTP 500, got HTTP 400",
                     "error: X.lean:3:4: unknown identifier JSONDecodeError",
                     "FAIL [repository]: fixture expects HTTP 500 but behavior changed",
                     "FAIL: test_retry (test_x.T.test_retry) gh: HTTP 503",
                     "guard: FAIL - lean-toolchain moves to a release candidate"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:02:00", "unexpected end of JSON input"), ("10:03:00", line)),
                                 retry.DETERMINISTIC)

    def test_the_allowlist(self):
        for line in ("unexpected end of JSON input",
                     "invalid character '<' looking for beginning of value",
                     "RuntimeError: gh api repos/o/r/tags?per_page=100 failed: gh: HTTP 503"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:03:00", line)), retry.TRANSIENT)

    def test_everything_else_is_unknown(self):
        # Plausible infrastructure messages not seen here yet: no re-run.
        for line in ("gh: HTTP 503", "gh: Service Unavailable (HTTP 503)",
                     "guard: FAIL - gh api repos/o/r/tags failed: gh: HTTP 504",
                     "##[error]gh api repos/o/r/compare/a...b failed 5 times (502): gh: HTTP 502",
                     "gh api repos/o/r/compare/a...b failed: HTTP 502",
                     "gh api repos/o/r/compare/a...b failed: no answer",
                     "##[error]gh api repos/o/r/tags: rate limited for 900 s, longer than the guard waits: x",
                     "curl: (56) Recv failure: Connection reset by peer",
                     "fatal: unable to access 'https://github.com/o/r/': The requested URL returned error: 502",
                     "error: RPC failed; HTTP 502 curl 22 The requested URL returned error: 502",
                     "urllib.error.HTTPError: HTTP Error 503: Service Unavailable",
                     "urllib.error.URLError: <urlopen error [Errno 110] Connection timed out>",
                     "RuntimeError: gh api x failed: gh: HTTP 404",
                     " unexpected end of JSON input", "unexpected end of JSON input!",
                     "The hosted runner encountered an error while running your job. (Error Type: Disconnect)."):
            with self.subTest(line=line):
                self.assertNotEqual(self.kind(("10:03:00", line)), retry.TRANSIENT)

    def test_quoted_transport_words_are_not_infrastructure(self):
        # The guard quotes invalid file contents in its verdicts.
        self.assertEqual(self.kind(("10:03:00", "guard: FAIL - unexpected lean-toolchain content: 'gh: HTTP 503'")),
                         retry.DETERMINISTIC)
        self.assertEqual(self.kind(("10:03:00", "guard: FAIL - gh api x failed: gh: HTTP 503; also y")),
                         retry.DETERMINISTIC)
        for line in ("ValueError: unexpected lean-toolchain content: 'gh: HTTP 503'",
                     "RuntimeError: gh api x failed: gh: HTTP 404",
                     "gh api x failed: HTTP 404",
                     "gh api x failed: HTTP 403",
                     "gh api x failed: the answer lacks the content",
                     "gh api x failed: the answer lacks the merge-base",
                     "the compare answer has no merge-base SHA",
                     "##[error]gh api x failed 5 times (404): gh: Not Found (HTTP 404)",
                     "##[warning]gh api x: attempt 1 of 5 failed (502), retrying in 2 s: gh: HTTP 502"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:03:00", line)), retry.UNKNOWN)

    def test_more_than_one_failed_step_cannot_vouch_for_a_retry(self):
        steps = [dict(step) for step in self.STEPS]
        steps[2]["conclusion"] = "failure"  # an always() cleanup step failed too
        log = self.log(("10:02:00", "unexpected end of JSON input"), ("10:05:00", "##[group]Run cleanup"),
                       ("10:05:00", "##[endgroup]"), ("10:05:30", "FAIL [post]: cleanup failed"))
        self.assertEqual(retry.classify("failure", steps, [], log)[0], retry.UNKNOWN)

    def test_a_group_in_the_last_second_keeps_check_failures_only(self):
        # The step's own nested group in its last second: its Lean error counts.
        self.assertEqual(self.kind(("10:02:00", "unexpected end of JSON input"),
                                   ("10:05:00", "##[group]Run diagnostics"),
                                   ("10:05:00", "error: X.lean:3:4: unknown identifier 'x'")),
                         retry.DETERMINISTIC)
        # The next step's command block: its output cannot vouch for a retry...
        self.assertEqual(self.kind(("10:04:00", "KeyError: 'deps'"),
                                   ("10:05:00", "##[group]Run actions/upload-artifact"),
                                   ("10:05:00", "unexpected end of JSON input")), retry.UNKNOWN)
        # ...but the step's own earlier output still does.
        self.assertEqual(self.kind(("10:02:00", "unexpected end of JSON input"),
                                   ("10:05:00", "##[group]Run actions/upload-artifact"),
                                   ("10:05:00", "Uploaded.")), retry.TRANSIENT)

    def test_broad_words_alone_are_not_infrastructure(self):
        for line in ("json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)",
                     "the fixture expects HTTP 500 here", "Internal Server Error handling is untested",
                     "Traceback (most recent call last):"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:03:00", line)), retry.UNKNOWN)

    def test_guard_retry_that_recovers_then_fails_for_real(self):
        self.assertEqual(self.kind(
            ("10:02:00", "##[warning]gh api repos/o/r/contents/x: attempt 1 of 5 failed (502), "
                         "retrying in 2 s: gh: HTTP 502"),
            ("10:02:30", "guard: FAIL - lean-toolchain moves to a release candidate")), retry.DETERMINISTIC)

    def test_only_the_failed_steps_output_counts(self):
        log = [f"2026-11-23T{time}.5Z {line}\n" for time, line in (
            ("10:00:30", "unexpected end of JSON input"),
            ("10:00:59", "unexpected end of JSON input"),
            ("10:01:00", "##[group]Run scripts/check.sh build"),
            ("10:01:00", "\x1b[36;1mgrep -q 'gh: HTTP 503' log || echo 'FAIL [x]: y'\x1b[0m"),
            ("10:01:00", "env:"),
            ("10:01:00", "  NOTE: unexpected end of JSON input"),
            ("10:01:00", "##[endgroup]"),
            ("10:04:59", "##[error]Process completed with exit code 1."),
            ("10:05:00", "##[group]Run actions/upload-artifact"),
            ("10:05:00", "unexpected end of JSON input"),
            ("10:05:30", "error: X.lean:1:1: unknown identifier"))]
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.UNKNOWN)

    def test_the_command_block_is_recognised_once(self):
        # A group the step's output opens in its first second is output, not
        # a new step: the Lean error before it stays.
        self.assertEqual(self.kind(("10:01:00", "error: X.lean:3:4: type mismatch"),
                                   ("10:01:01", "##[group]Run diagnostic checks"),
                                   ("10:01:01", "##[endgroup]"),
                                   ("10:01:02", "unexpected end of JSON input")), retry.DETERMINISTIC)

    def test_without_a_command_block_the_log_cannot_vouch_for_a_retry(self):
        lines = [("10:00:59", "unexpected end of JSON input"), ("10:01:01", "Warning: invalid action input"),
                 ("10:02:00", "unexpected end of JSON input")]
        log = self.log(*lines, header=False)
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.UNKNOWN)
        log = self.log(("10:02:00", "error: X.lean:1:1: bad"), header=False)
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.DETERMINISTIC)
        # Nor can it vouch for the runner's report of losing the job.
        lost = ["The runner has received a shutdown signal. This can happen when the runner "
                "service is stopped, or a manually started runner is canceled."]
        self.assertEqual(retry.classify("cancelled", self.STEPS, lost, [])[0], retry.UNKNOWN)

    def test_errors_without_a_location_are_check_failures(self):
        # Lean and Lake also report errors without a location: next to an
        # allowlisted line, such a line still makes the failure deterministic.
        for line in ("error: build failed", "error: unknown module prefix 'X'",
                     "  error: X: bad import", "Error: something", "ERROR: x"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:01:01", "unexpected end of JSON input"),
                                           ("10:01:02", line)), retry.DETERMINISTIC)
        for line in ("errors: 0", "error_count=0", "no error found"):
            with self.subTest(line=line):
                self.assertEqual(self.kind(("10:01:01", "unexpected end of JSON input"),
                                           ("10:01:02", line)), retry.TRANSIENT)

    def test_a_group_opened_by_the_steps_output_is_still_read(self):
        self.assertEqual(self.kind(("10:02:00", "##[group]Run the next check"),
                                   ("10:02:01", "error: MathlibExt/A.lean:3:4: unknown identifier 'x'"),
                                   ("10:02:02", "##[endgroup]")), retry.DETERMINISTIC)

    def test_an_unreadable_log_is_unknown(self):
        log = self.log(("10:02:00", "unexpected end of JSON input")) + [retry.INCOMPLETE]
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.UNKNOWN)
        log = self.log(("10:02:00", "error: A.lean:1:1: bad")) + [retry.INCOMPLETE]
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.DETERMINISTIC)
        # A log that cannot be fetched at all vouches for nothing: a runner
        # annotation cannot be checked against the step's end.
        lost = ["The runner has received a shutdown signal. This can happen when the runner "
                "service is stopped, or a manually started runner is canceled."]
        self.assertEqual(retry.classify("failure", self.STEPS, lost, [retry.UNAVAILABLE])[0], retry.UNKNOWN)
        self.assertEqual(retry.classify("cancelled", self.STEPS, [], [retry.UNAVAILABLE])[0], retry.UNKNOWN)
        self.assertEqual(retry.classify("failure", self.STEPS, ["Process completed with exit code 1."],
                                        [retry.UNAVAILABLE])[0], retry.UNKNOWN)
        # More than one failed step vetoes the fallback too.
        steps = [dict(step) for step in self.STEPS]
        steps[2]["conclusion"] = "cancelled"
        self.assertEqual(retry.classify("cancelled", steps, [], [retry.UNAVAILABLE])[0], retry.UNKNOWN)
        # Once the step's output has been read, an unreadable rest does not matter.
        log = self.log(("10:02:00", "unexpected end of JSON input"),
                       ("10:05:01", "Post job cleanup.")) + [retry.INCOMPLETE]
        self.assertEqual(retry.classify("failure", self.STEPS, [], log)[0], retry.TRANSIENT)

    def test_lost_runner_is_transient_and_a_plain_cancellation_unknown(self):
        lost = ["The runner has received a shutdown signal. This can happen when the runner "
                "service is stopped, or a manually started runner is canceled."]
        self.assertEqual(self.kind(("10:03:00", "Building..."), annotations=lost), retry.TRANSIENT)
        self.assertEqual(self.kind(("10:03:00", "Building..."), annotations=lost, conclusion="cancelled"),
                         retry.TRANSIENT)
        # Who cancelled is not visible: a cancellation alone, even after an
        # allowlisted line, is no evidence.
        self.assertEqual(self.kind(conclusion="cancelled"), retry.UNKNOWN)
        self.assertEqual(self.kind(("10:03:00", "unexpected end of JSON input"), conclusion="cancelled"),
                         retry.UNKNOWN)
        self.assertEqual(self.kind(("10:03:00", "error: A.lean:1:1: bad"), annotations=lost), retry.DETERMINISTIC)

    def test_a_runner_message_from_a_step_that_ended_on_its_own_does_not_count(self):
        # A step can print "::error::The runner has received a shutdown signal";
        # the runner then still writes the step's exit code.
        lost = ["The runner has received a shutdown signal. This can happen when the runner "
                "service is stopped, or a manually started runner is canceled."]
        self.assertEqual(self.kind(("10:03:00", "##[error]The runner has received a shutdown signal."),
                                   ("10:04:59", "##[error]Process completed with exit code 1."),
                                   annotations=lost), retry.UNKNOWN)
        self.assertEqual(self.kind(("10:03:00", "##[error]The runner has received a shutdown signal.")),
                         retry.UNKNOWN)
        # An exit in the step's ambiguous last second still vetoes it.
        self.assertEqual(self.kind(("10:05:00", "##[group]Run diagnostics"),
                                   ("10:05:00", "##[error]Process completed with exit code 1."),
                                   annotations=lost), retry.UNKNOWN)
        # So does a log with no step output at all.
        self.assertEqual(retry.classify("failure", self.STEPS, lost, [])[0], retry.UNKNOWN)

    def test_githubs_internal_error_annotation_counts(self):
        internal = ["GitHub Actions has encountered an internal error when running your job."]
        self.assertEqual(self.kind(("10:03:00", "Building..."), annotations=internal), retry.TRANSIENT)
        self.assertEqual(self.kind(("10:03:00", "Building..."),
                                   ("10:04:59", "##[error]Process completed with exit code 1."),
                                   annotations=internal), retry.UNKNOWN)

    def test_a_runner_message_needs_the_steps_closed_command_block(self):
        lost = ["The runner has received a shutdown signal. This can happen when the runner "
                "service is stopped, or a manually started runner is canceled."]
        log = [f"2026-11-23T10:01:00.1Z ##[group]Run scripts/check.sh build\n"]
        self.assertEqual(retry.classify("failure", self.STEPS, lost, log)[0], retry.UNKNOWN)

    def test_a_job_cancelled_for_running_too_long_is_unknown(self):
        internal = "GitHub Actions has encountered an internal error when running your job."
        for annotation in ("The job running on runner GitHub Actions 12 has exceeded the maximum execution "
                           "time of 360 minutes.", "The action 'Build' has timed out after 30 minutes.",
                           "The run was canceled by @someone.",
                           "Canceling since a higher priority waiting request for 'CI-x' exists"):
            with self.subTest(annotation=annotation):
                for conclusion in ("cancelled", "failure"):
                    self.assertEqual(self.kind(annotations=[annotation], conclusion=conclusion), retry.UNKNOWN)
                    self.assertEqual(self.kind(("10:03:00", "unexpected end of JSON input"),
                                               annotations=[annotation], conclusion=conclusion), retry.UNKNOWN)
                    self.assertEqual(self.kind(("10:03:00", "Building..."), annotations=[annotation, internal],
                                               conclusion=conclusion), retry.UNKNOWN)
                    self.assertEqual(retry.classify(conclusion, self.STEPS, [annotation],
                                                    [retry.UNAVAILABLE])[0], retry.UNKNOWN)
                self.assertEqual(self.kind(("10:03:00", "error: A.lean:1:1: bad"), annotations=[annotation],
                                           conclusion="cancelled"), retry.DETERMINISTIC)

    def test_a_timed_out_job_is_unknown(self):
        # It would most likely time out again, and the queue stops waiting after 6 hours.
        self.assertEqual(self.kind(conclusion="timed_out"), retry.UNKNOWN)
        self.assertEqual(self.kind(("10:03:00", "unexpected end of JSON input"),
                                   conclusion="timed_out"), retry.UNKNOWN)
        self.assertEqual(self.kind(("10:03:00", "error: A.lean:1:1: bad"), conclusion="timed_out"),
                         retry.DETERMINISTIC)
        expired = ["The job running on runner GitHub Actions 12 has exceeded the maximum execution "
                   "time of 360 minutes."]
        self.assertEqual(self.kind(annotations=expired), retry.UNKNOWN)

    def test_a_plain_exit_code_is_unknown(self):
        self.assertEqual(self.kind(("10:03:00", "KeyError: 'deps'"),
                                   annotations=["Process completed with exit code 1."]), retry.UNKNOWN)


class JobLog(unittest.TestCase):
    """Api.job_log reads a bounded log and marks what it could not read."""

    class Response(io.BytesIO):
        code = 200
        headers: dict = {}

    def lines(self, response=None, error=None, limit=None):
        api = retry.Api("token")
        api._open = mock.Mock(side_effect=error, return_value=response)
        with mock.patch.object(retry, "LOG_LIMIT", limit or retry.LOG_LIMIT):
            return list(api.job_log(REPO, 1))

    def test_complete_log(self):
        self.assertEqual(self.lines(self.Response(b"a\nb\n")), ["a\n", "b\n"])

    def test_cap_download_errors_and_bad_status(self):
        self.assertEqual(self.lines(self.Response(b"gh: HTTP 503\nerror: A.lean:1:1: x\n"), limit=14),
                         ["gh: HTTP 503\n", retry.INCOMPLETE])
        self.assertEqual(self.lines(error=urllib.error.URLError("offline")), [retry.UNAVAILABLE])
        gone = self.Response(b"")
        gone.code = 410
        self.assertEqual(self.lines(gone), [retry.UNAVAILABLE])

    def test_a_response_shorter_than_its_length_is_incomplete(self):
        import http.client
        body = b"gh: HTTP 503\n"
        raw = b"HTTP/1.1 200 OK\r\nContent-Length: 45\r\n\r\n" + body

        class Socket:
            def makefile(self, mode):
                return io.BytesIO(raw)
        response = http.client.HTTPResponse(Socket())
        response.begin()
        self.assertEqual(self.lines(response), ["gh: HTTP 503\n", retry.INCOMPLETE])
        complete = self.Response(body)
        complete.headers = {"Content-Length": str(len(body))}
        self.assertEqual(self.lines(complete), ["gh: HTTP 503\n"])

    def test_an_oversized_line_is_incomplete_evidence(self):
        # Read in bounded pieces; only the first is kept, as a LongLine, and
        # the middle of the line is never yielded.
        middle = b"gh: HTTP 503\n"
        line = b"x" * retry.LINE_LIMIT + middle[:-1] + b"y" * retry.LINE_LIMIT + b"\n"
        lines = self.lines(self.Response(line + middle))
        self.assertEqual(lines, ["x" * retry.LINE_LIMIT, "gh: HTTP 503\n"])
        self.assertIsInstance(lines[0], retry.LongLine)
        self.assertEqual(self.lines(self.Response(b"z" * (2 * retry.LINE_LIMIT))), ["z" * retry.LINE_LIMIT])
        # In the failed step's output it makes the failure unknown, whatever its start says.
        steps = Classify.STEPS
        head = ["2026-11-23T10:01:00.1Z ##[group]Run build\n", "2026-11-23T10:01:00.2Z ##[endgroup]\n"]
        long_line = retry.LongLine("2026-11-23T10:02:00.0Z unexpected end of JSON input" + "x" * 100)
        self.assertEqual(retry.classify("failure", steps, [], head + [long_line])[0], retry.UNKNOWN)
        with_error = head + [long_line, "2026-11-23T10:03:00.0Z error: A.lean:1:1: bad\n"]
        self.assertEqual(retry.classify("failure", steps, [], with_error)[0], retry.DETERMINISTIC)


class QueueBranch(unittest.TestCase):
    def test_parses_main_merge_group_refs_only(self):
        base = "e6acc6d2dbed5de71d67fe25399bf7d652e9db0c"
        self.assertEqual(retry.queue_branch(f"gh-readonly-queue/main/pr-6624-{base}"), (6624, base))
        for name in (f"gh-readonly-queue/main/pr-0624-{base}", f"gh-readonly-queue/main/pr-6624-{base.upper()}",
                     f"gh-readonly-queue/main/pr-6624-{base[:39]}", f"gh-readonly-queue/main/pr-6624-{base}x",
                     f"gh-readonly-queue/main/pr-6624-{base}\n", f"gh-readonly-queue/dev/pr-6624-{base}",
                     f"refs/heads/gh-readonly-queue/main/pr-6624-{base}", f"gh-readonly-queue/main/pr-\u0666-{base}",
                     f"gh-readonly-queue/main/pr-12345678-{base}", "main", None, 6624):
            with self.subTest(name=name):
                self.assertIsNone(retry.queue_branch(name))

    def test_text_is_an_inert_code_span(self):
        self.assertEqual(retry.text("a `b` | @c\n<d>\u202e"), "`a 'b' / @c <d>`")
        self.assertEqual(retry.text("x" * 200, 10), "`" + "x" * 9 + "\u2026`")


class Triage(unittest.TestCase):
    def guard_alone(self, api: FakeApi, pr: int) -> None:
        """The moment `guard` failed: the PR's CI was still running."""
        for name in ("build", "repository integrity", "check the graph"):
            api.check(GROUPS[pr][0], name, status="in_progress", conclusion=None)

    def test_transient_guard_failure_is_rerun_once_in_active_mode(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(report.decision, "retry")
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])
        # The run is read again, then the entry last, right before the re-run.
        reads = [c for c in api.calls if c in (("GET", f"{API}/actions/runs/45239318416"),) or c[0] == "GRAPHQL"]
        self.assertEqual([c[0] for c in reads], ["GRAPHQL", "GET", "GET", "GRAPHQL"])
        self.assertEqual(api.calls[-1][0], "POST")

    def test_dry_run_reruns_nothing(self):
        for pr in (6624, 4431):
            with self.subTest(pr=pr):
                api = FakeApi({pr: entry(pr)})
                report = quiet(retry.triage, api, REPO, pr, "dry-run", trigger(pr))
                self.assertEqual((report.decision, api.posts()), ("retry", []))
                self.assertIn("would re-run the failed jobs", summary(report))

    def test_failed_check_in_a_running_workflow_counts(self):
        # #6651 between 17:43:45 and 18:04:56: guard failed (503), repository
        # integrity failed a test, build still running.
        api = FakeApi({6651: entry(6651)})
        api.check(GROUPS[6651][0], "build", status="in_progress", conclusion=None)
        run = api.responses[f"GET {API}/actions/runs/45230586597"]
        run.update(status="in_progress", conclusion=None)
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual(api.posts(), [])
        self.assertEqual(sorted((f.check, f.kind) for f in report.failures),
                         [("guard", retry.TRANSIENT), ("repository integrity", retry.DETERMINISTIC)])
        self.assertEqual(report.decision, "observe")

    def split_rules(self, api: FakeApi, moved: str) -> tuple[list, list]:
        """main's recorded rules on a full first page, the rule for `moved` on a second.

        The rule requiring the other checks stays on page one; 100 rules of
        another type fill the page.
        """
        rules = api.responses[f"GET {API}/rules/branches/main?per_page=100&page=1"]
        checks = next(r for r in rules if r["type"] == "required_status_checks")
        first, second = copy.deepcopy(checks), copy.deepcopy(checks)
        first["parameters"]["required_status_checks"] = [
            c for c in checks["parameters"]["required_status_checks"] if c["context"] != moved]
        second["parameters"]["required_status_checks"] = [
            c for c in checks["parameters"]["required_status_checks"] if c["context"] == moved]
        page = [first if rule is checks else rule for rule in rules]
        page += [{"type": "deletion", "parameters": {}}] * (100 - len(page))
        return page, [second]

    def test_a_required_check_rule_on_page_two_counts(self):
        # #6651 between 17:43:45 and 18:04:56 (guard failed on a 503, repository
        # integrity failed a test, build still running), with the rule that
        # requires repository integrity on the second page of main's rules.
        def at_the_time():
            api = FakeApi({6651: entry(6651)})
            api.check(GROUPS[6651][0], "build", status="in_progress", conclusion=None)
            api.responses[f"GET {API}/actions/runs/45230586597"].update(status="in_progress",
                                                                        conclusion=None)
            return api
        page = f"GET {API}/rules/branches/main?per_page=100&page={{}}"
        api = at_the_time()
        first, second = self.split_rules(api, "repository integrity")
        api.responses[page.format(1)], api.responses[page.format(2)] = first, second
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertIn(("GET", page.format(2)[4:]), api.calls)
        self.assertEqual(api.posts(), [])
        self.assertEqual(sorted((f.check, f.kind) for f in report.failures),
                         [("guard", retry.TRANSIENT), ("repository integrity", retry.DETERMINISTIC)])
        # Had page two been missed, repository integrity would be missing from
        # the rules read, and since the repository declares it required,
        # nothing would be decided either.
        api = at_the_time()
        api.responses[page.format(1)] = first[:-1]  # a short page: no page two
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def layered_rules(self, api: FakeApi, apps: tuple) -> None:
        """main's recorded rules, requiring repository integrity from apps[0], on a
        full first page, and a rule requiring it from apps[1] on a second."""
        page = f"GET {API}/rules/branches/main?per_page=100&page={{}}"
        rules = copy.deepcopy(api.responses[page.format(1)])
        checks = next(r for r in rules if r["type"] == "required_status_checks")
        for check in checks["parameters"]["required_status_checks"]:
            if check["context"] == "repository integrity":
                check["integration_id"] = apps[0]
        rules += [{"type": "deletion", "parameters": {}}] * (100 - len(rules))
        extra = {"type": "required_status_checks", "parameters": {"required_status_checks": [
            {"context": "repository integrity", "integration_id": apps[1]}]}}
        api.responses[page.format(1)], api.responses[page.format(2)] = rules, [extra]

    def test_one_check_required_from_two_apps_is_undecidable(self):
        # Rulesets are layered, so every requirement applies: another app's
        # passing repository integrity must not hide the GitHub Actions job's
        # failure (#6651 between 17:43:45 and 18:04:56), whichever rule comes
        # last. The same app twice is one requirement.
        actions, other = retry.GITHUB_ACTIONS_APP, 4242
        for apps, decision in (((actions, other), "unknown"), ((other, actions), "unknown"),
                               (("15368", actions), "unknown"), ((True, actions), "unknown"),
                               ((False, actions), "unknown"), ((actions, True), "unknown"),
                               ((actions, actions), "observe")):
            with self.subTest(apps=apps):
                api = FakeApi({6651: entry(6651)})
                head = GROUPS[6651][0]
                api.check(head, "build", status="in_progress", conclusion=None)
                api.responses[f"GET {API}/actions/runs/45230586597"].update(status="in_progress",
                                                                            conclusion=None)
                data = api.responses[f"GET {checks_path(head)}"]
                integrity = next(c for c in data["check_runs"] if c["name"] == "repository integrity")
                data["check_runs"].append(dict(integrity, id=integrity["id"] + 7, conclusion="success",
                                               app={"id": other, "slug": "other"}))
                self.layered_rules(api, apps)
                report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
                self.assertEqual((api.posts(), report.decision), ([], decision))
                if decision == "unknown":
                    self.assertFalse([call for call in api.calls if call[0] in ("GRAPHQL", "LOG")])

    def test_a_malformed_app_id_is_undecidable(self):
        # A single rule requiring repository integrity from an app id that is
        # not an integer (JSON true/false, a string): #6651 between 17:43:45
        # and 18:04:56 must not re-run guard while integrity has failed.
        for app in (True, False, "15368", 15368.0):
            with self.subTest(app=app):
                api = FakeApi({6651: entry(6651)})
                api.check(GROUPS[6651][0], "build", status="in_progress", conclusion=None)
                api.responses[f"GET {API}/actions/runs/45230586597"].update(status="in_progress",
                                                                            conclusion=None)
                next(c for c in self.rules(api) if c["context"] == "repository integrity")["integration_id"] = app
                report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))
                self.assertFalse([call for call in api.calls if call[0] in ("GRAPHQL", "LOG")])

    def test_rules_that_change_before_the_rerun_stop_it(self):
        # While the guard job is classified, a rule starts requiring another
        # check, changes guard's app, or gains more pages than are read.
        key = f"GET {API}/rules/branches/main?per_page=100&page=1"
        for change in ("added", "app", "pages"):
            with self.subTest(change=change):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)

                def edit_rules(path, api=api, change=change):
                    if path != f"{API}/actions/jobs/{GROUPS[6624][3]}":
                        return
                    rules = api.responses[key]
                    checks = next(r for r in rules if r["type"] == "required_status_checks")
                    contexts = checks["parameters"]["required_status_checks"]
                    if change == "added":
                        contexts.append({"context": "test the site scripts", "integration_id": 15368})
                    elif change == "app":
                        next(c for c in contexts if c["context"] == "guard")["integration_id"] = None
                    else:
                        filler = [{"type": "deletion", "parameters": {}}] * 100
                        api.responses[key] = (rules + filler)[:100]
                        for number in range(2, retry.RULE_PAGES + 1):
                            api.responses[f"GET {API}/rules/branches/main?per_page=100&page={number}"] = filler
                api.before_get = edit_rules
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual(api.posts(), [])
                self.assertIn("the checks main's rules require changed", summary(report))

    def test_declared_checks_match_the_repository_inventory(self):
        source = (ROOT / "scripts" / "test_merge_queue_checks.py").read_text()
        assignment = next(node for node in ast.parse(source).body if isinstance(node, ast.Assign)
                          and any(getattr(t, "id", None) == "REQUIRED" for t in node.targets))
        self.assertEqual(sorted(retry.DECLARED), sorted(ast.literal_eval(assignment.value)))

    def test_rules_that_omit_a_declared_check_are_undecidable(self):
        # The check the graph failed while guard failed transiently (#6624). With
        # the graph required, its failure counts; with main's rules omitting it,
        # nothing is decided, since another source could require it.
        head = GROUPS[6624][0]
        graph = 137919366205  # the check the graph's check run on #6624's merge group
        for omitted in (False, True):
            with self.subTest(omitted=omitted):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.check(head, "check the graph", status="completed", conclusion="failure")
                api.responses[f"GET {API}/actions/jobs/{graph}"] = {"run_id": None}
                if omitted:
                    checks = self.rules(api)
                    checks[:] = [c for c in checks if c["context"] != "check the graph"]
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual(api.posts(), [])
                if omitted:
                    self.assertEqual(report.decision, "unknown")
                    self.assertIn("which this repository declares required", summary(report))
                else:
                    self.assertIn(("check the graph", retry.UNKNOWN),
                                  [(f.check, f.kind) for f in report.failures])

    def test_more_rule_pages_than_are_read_fail_closed(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        page = f"GET {API}/rules/branches/main?per_page=100&page={{}}"
        filler = [{"type": "deletion", "parameters": {}}] * 100
        api.responses[page.format(1)] = (api.responses[page.format(1)] + filler)[:100]
        for number in range(2, retry.RULE_PAGES + 1):
            api.responses[page.format(number)] = filler
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))
        self.assertIn("a required check could be missed", summary(report))
        self.assertFalse([call for call in api.calls if call[0] in ("GRAPHQL", "LOG")])

    def test_json_booleans_are_not_integers(self):
        self.assertTrue(retry.integer(1))
        for value in (True, False, 1.0, "1", None):
            self.assertFalse(retry.integer(value))
        # A run whose attempt reads as true is not taken for a first attempt.
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.responses[f"GET {API}/actions/runs/45239318416"]["run_attempt"] = True
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_every_page_of_check_runs_is_read(self):
        # #6651 between 17:43:45 and 18:04:56, with repository integrity's failed
        # check run on a second page and no total_count: a full first page means
        # reading the next one.
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        api.check(head, "build", status="in_progress", conclusion=None)
        api.responses[f"GET {API}/actions/runs/45230586597"].update(status="in_progress", conclusion=None)
        first = api.responses[f"GET {checks_path(head)}"]["check_runs"]
        integrity = next(c for c in first if c["name"] == "repository integrity")
        first.remove(integrity)
        first += [{"id": 9 * 10**11 + i, "name": f"filler {i}", "head_sha": head, "status": "completed",
                   "conclusion": "success", "app": {"id": 15368, "slug": "github-actions"}}
                  for i in range(100 - len(first))]
        api.responses[f"GET {checks_path(head)}"] = {"check_runs": first}
        second = f"{API}/commits/{head}/check-runs?filter=latest&per_page=100&page=2"
        api.responses[f"GET {second}"] = {"check_runs": [integrity]}
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertIn(("GET", second), api.calls)
        self.assertEqual(api.posts(), [])
        self.assertEqual(sorted((f.check, f.kind) for f in report.failures),
                         [("guard", retry.TRANSIENT), ("repository integrity", retry.DETERMINISTIC)])

    def at_6651(self) -> FakeApi:
        """#6651 between 17:43:45 and 18:04:56: guard failed on a 503, repository
        integrity failed a test, build still running."""
        api = FakeApi({6651: entry(6651)})
        api.check(GROUPS[6651][0], "build", status="in_progress", conclusion=None)
        api.responses[f"GET {API}/actions/runs/45230586597"].update(status="in_progress", conclusion=None)
        return api

    def assert_undecided(self, api: FakeApi, pr: int = 6651) -> retry.Report:
        report = quiet(retry.triage, api, REPO, pr, "active", trigger(pr))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))
        return report

    def test_a_required_check_run_that_cannot_be_identified_is_undecidable(self):
        head = GROUPS[6651][0]
        cases = [{"id": value} for value in (True, False, "x", None)]
        cases += [{"app": value} for value in ({"id": True}, {"id": "15368"}, None, "x", {})]
        cases += [{"status": value} for value in (None, "weird", True)]
        for change in cases:
            with self.subTest(change=change):
                api = self.at_6651()
                api.check(head, "repository integrity", **change)
                self.assert_undecided(api)
                self.assertFalse([call for call in api.calls if call[0] == "LOG"])
        for row in ({"id": 1, "name": None, "status": "completed"}, "x", None):
            with self.subTest(row=row):
                api = self.at_6651()
                api.responses[f"GET {checks_path(head)}"]["check_runs"].append(row)
                self.assert_undecided(api)

    def test_a_malformed_page_of_check_runs_is_undecidable(self):
        # A full first page with guard's transient failure; repository
        # integrity's failure would be on the second page, which is unreadable.
        head = GROUPS[6651][0]
        second = f"GET {API}/commits/{head}/check-runs?filter=latest&per_page=100&page=2"
        for page in ({}, {"check_runs": None}, {"check_runs": {}}, [], "text"):
            with self.subTest(page=page):
                api = self.at_6651()
                data = api.responses[f"GET {checks_path(head)}"]
                first = [c for c in data["check_runs"] if c["name"] != "repository integrity"]
                first += [{"id": 9 * 10**11 + i, "name": f"filler {i}", "status": "completed",
                           "conclusion": "success", "app": {"id": 15368}} for i in range(100 - len(first))]
                data["check_runs"] = first
                api.responses[second] = page
                self.assert_undecided(api)
        api = self.at_6651()
        api.responses[f"GET {checks_path(head)}"] = {"total_count": 8}  # no check_runs at all
        self.assert_undecided(api)

    def test_a_malformed_required_checks_rule_is_undecidable(self):
        key = f"GET {API}/rules/branches/main?per_page=100&page=1"
        for parameters in ({}, None, {"required_status_checks": None}, {"required_status_checks": {}},
                           {"required_status_checks": ["guard"]},
                           {"required_status_checks": [{"context": None, "integration_id": 15368}]}):
            with self.subTest(parameters=parameters):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.responses[key].append({"type": "required_status_checks", "parameters": parameters})
                self.assert_undecided(api, 6624)
                self.assertFalse([call for call in api.calls if call[0] in ("GRAPHQL", "LOG")])
        api = FakeApi({6624: entry(6624)})
        api.responses[key].append("x")
        self.assert_undecided(api, 6624)

    def test_unreadable_annotations_block_the_rerun(self):
        key = f"GET {API}/check-runs/{GROUPS[6624][3]}/annotations?per_page=50&page=1"
        for page in ({}, [{"message": None}], ["x"], [{}], None):
            with self.subTest(page=page):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.responses[key] = page
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))
                self.assertIn("unreadable annotations", summary(report))

    def test_a_failed_step_without_a_known_start_or_end_is_unknown(self):
        for field in ("started_at", "completed_at"):
            with self.subTest(field=field):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                job = api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]
                next(step for step in job["steps"] if step["conclusion"] == "failure")[field] = None
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_a_job_that_disagrees_with_its_check_run_is_unknown(self):
        for conclusion in (True, "success", None, "cancelled"):
            with self.subTest(conclusion=conclusion):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]["conclusion"] = conclusion
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_unreadable_steps_are_unknown(self):
        def steps_of(api):
            return api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]
        changes = [lambda job: job.update(steps={}), lambda job: job.update(steps=None),
                   lambda job: job.update(steps=["x"]),
                   lambda job: job["steps"][0].update(conclusion=True),
                   lambda job: [step.update(conclusion="success") for step in job["steps"]]]
        for number, change in enumerate(changes):
            with self.subTest(case=number):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                change(steps_of(api))
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_a_required_check_reported_by_a_commit_status_is_undecidable(self):
        # A rule may accept a commit status for a required check; this job reads
        # check runs only, so any such status leaves the decision to the queue.
        head = GROUPS[6624][0]
        statuses = f"GET {API}/commits/{head}/status?per_page=100&page=1"
        for context, state in (("external policy", "failure"), ("external policy", "success"),
                               ("External Policy", "failure"), (" external  policy ", "failure"),
                               ("guard", "success"), ("GUARD", "success"), ("build", "pending")):
            with self.subTest(context=context, state=state):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                self.rules(api).append({"context": "external policy", "integration_id": None})
                api.responses[statuses]["statuses"] = [{"context": context, "state": state}]
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))
                self.assertIn("a commit status reports", summary(report))
        for page in ({}, {"statuses": None}, {"statuses": [{"context": None, "state": "success"}]},
                     {"statuses": [{"context": "x", "state": "weird"}]}, [], "text"):
            with self.subTest(page=page):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.responses[statuses] = page
                self.assertEqual(quiet(retry.triage, api, REPO, 6624, "active", trigger(6624)).decision,
                                 "unknown")
                self.assertEqual(api.posts(), [])
        # A status of a check that is not required changes nothing.
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.responses[statuses]["statuses"] = [{"context": "deploy preview", "state": "failure"}]
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_a_commit_status_that_appears_before_the_rerun_stops_it(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        statuses = f"GET {API}/commits/{GROUPS[6624][0]}/status?per_page=100&page=1"

        def status_appears(path):
            if path == f"{API}/actions/jobs/{GROUPS[6624][3]}":
                api.responses[statuses]["statuses"] = [{"context": "guard", "state": "failure"}]
        api.before_get = status_appears
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("required checks changed", summary(report))

    def test_a_check_run_whose_status_and_conclusion_disagree_is_undecidable(self):
        # #6651's repository integrity reported running yet failed, or
        # completed without a conclusion.
        head = GROUPS[6651][0]
        for fields in ({"status": "in_progress", "conclusion": "failure"},
                       {"status": "queued", "conclusion": "success"},
                       {"status": "completed", "conclusion": None}):
            with self.subTest(fields=fields):
                api = self.at_6651()
                api.check(head, "repository integrity", **fields)
                self.assert_undecided(api)

    def test_a_job_that_is_not_the_check_runs_job_is_unknown(self):
        # The job read for guard's check run must be that check run's job:
        # same id and name, completed, with an integer attempt. Another job's
        # answer (here CI's build job of #6651, with its run) is not used.
        ci_job = {"id": 137888725562, "name": "build", "run_id": 45230586597}
        changes = [{"id": 1}, {"name": "build"}, {"status": "in_progress"}, {"run_attempt": True},
                   {"run_attempt": None}, ci_job]
        for change in changes:
            with self.subTest(change=change):
                api = FakeApi({6651: entry(6651)})
                self.guard_alone(api, 6651)
                api.responses[f"GET {API}/actions/jobs/{GROUPS[6651][3]}"].update(change)
                report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_a_completed_step_needs_a_conclusion(self):
        # guard's allowlisted failure (#6624) followed by a failed cleanup step
        # is more than one failed step; a completed cleanup step whose
        # conclusion is missing or null cannot vouch that it did not fail.
        def with_cleanup(**fields):
            api = FakeApi({6624: entry(6624)})
            self.guard_alone(api, 6624)
            job = api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]
            step = dict(job["steps"][-1], name="Clean up", number=99, **fields)
            if fields.get("conclusion", "") is ...:
                del step["conclusion"]
            job["steps"].append(step)
            return api
        cases = [{"status": "completed", "conclusion": "failure"},
                 {"status": "completed", "conclusion": "action_required"},
                 {"status": "completed", "conclusion": "timed_out"},
                 {"status": "completed", "conclusion": None},
                 {"status": "completed", "conclusion": ...},
                 {"status": "in_progress", "conclusion": "success"},
                 {"status": None, "conclusion": "success"}]
        for fields in cases:
            with self.subTest(fields=fields):
                api = with_cleanup(**fields)
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))
        # A cleanup step that succeeded leaves guard's failure the only one.
        api = with_cleanup(status="completed", conclusion="success")
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_an_error_without_a_location_next_to_an_allowlisted_line_blocks_the_rerun(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        job = GROUPS[6624][3]
        lines = (FIXTURES / "logs" / f"{job}.txt").read_text(encoding="utf-8").splitlines(True)
        at = next(i for i, line in enumerate(lines) if line.endswith(" unexpected end of JSON input\n"))
        lines.insert(at + 1, lines[at].replace("unexpected end of JSON input", "error: build failed"))
        api.logs[job] = lines
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertEqual([(f.check, f.kind) for f in report.failures], [("guard", retry.DETERMINISTIC)])

    def test_a_failed_step_that_needs_action_is_unknown(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        job = api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]
        next(step for step in job["steps"] if step["conclusion"] == "failure")["conclusion"] = "action_required"
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_names_that_differ_from_a_required_check_only_in_case_are_undecidable(self):
        # GitHub may match a check's name regardless of case or spacing: a check
        # run or a rule spelled differently cannot be told apart from a
        # required check, so nothing is decided.
        head = GROUPS[6624][0]
        for name in ("Repository Integrity", "guard ", "check  the graph"):
            with self.subTest(check_run=name):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.responses[f"GET {checks_path(head)}"]["check_runs"].append(
                    {"id": 5, "name": name, "status": "completed", "conclusion": "failure",
                     "app": {"id": 15368}})
                report = self.assert_undecided(api, 6624)
                self.assertIn("only in case or spacing", summary(report))
        for context in ("Guard", "build "):
            with self.subTest(rule=context):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                self.rules(api).append({"context": context, "integration_id": 15368})
                report = self.assert_undecided(api, 6624)
                self.assertIn("only in case or spacing", summary(report))

    def test_an_unreadable_answer_while_revalidating_stops_the_rerun(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        key = f"GET {checks_path(GROUPS[6624][0])}"

        def break_the_page(path):
            if path == f"{API}/actions/jobs/{GROUPS[6624][3]}":
                api.responses[key] = {"check_runs": None}
        api.before_get = break_the_page
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("required checks changed", summary(report))

    def test_transient_guard_alone_while_ci_runs_is_rerun(self):
        # #6651 at 17:43:11: only guard had failed.
        api = FakeApi({6651: entry(6651)})
        self.guard_alone(api, 6651)
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual(api.posts(), [RERUN.format(45230586519)])
        self.assertEqual([f.check for f in report.failures], ["guard"])

    def test_transient_failure_in_a_running_workflow_waits_for_it(self):
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.responses[f"GET {API}/actions/runs/45239318416"].update(status="in_progress", conclusion=None)
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("still running", summary(report))

    def test_second_attempt_is_not_rerun(self):
        api = FakeApi({6624: entry(6624)})
        api.responses[f"GET {API}/actions/runs/45239318416"]["run_attempt"] = 2
        api.responses[f"GET {API}/actions/jobs/137919366370"]["run_attempt"] = 2
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624, attempt=2))
        self.assertEqual(api.posts(), [])
        self.assertIn("already re-run (attempt 2)", summary(report))

    def test_not_queued_or_no_group_means_no_action(self):
        for queue_entry in (None, {"position": 3, "state": "UNMERGEABLE", "headCommit": None,
                                   "baseCommit": {"oid": GROUPS[6624][1]}}):
            with self.subTest(entry=queue_entry):
                api = FakeApi({6624: queue_entry})
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "none"))
                self.assertFalse([c for c in api.calls if c[0] == "LOG"])

    def test_stale_trigger_checks_only_the_current_group(self):
        newer = "a" * 40
        api = FakeApi({6624: entry(6624, head=newer)})
        api.responses[f"GET {checks_path(newer)}"] = {"total_count": 0, "check_runs": []}
        api.responses[f"GET {API}/commits/{newer}/status?per_page=100&page=1"] = {"statuses": []}
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("older merge group", summary(report))
        self.assertNotIn(("GET", checks_path(GROUPS[6624][0])), api.calls)

    def test_a_check_that_fails_while_classifying_stops_the_rerun(self):
        # #6651: repository integrity, still running when the checks were
        # first read, fails while the guard job is being classified.
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        self.guard_alone(api, 6651)

        def integrity_fails(path):
            if path == f"{API}/actions/jobs/{GROUPS[6651][3]}":
                api.check(head, "repository integrity", status="completed", conclusion="failure")
        api.before_get = integrity_fails
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual(api.posts(), [])
        self.assertIn("required checks changed", summary(report))

    def test_a_timed_out_build_is_not_rerun(self):
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        api.check(head, "repository integrity", conclusion="success")
        api.check(head, "build", conclusion="timed_out")
        job = api.responses[f"GET {API}/actions/jobs/137888725562"]
        job["conclusion"] = "timed_out"
        step = next(step for step in job["steps"] if step["conclusion"] == "failure")
        api.logs[137888725562] = [
            f"{step['started_at'][:19]}.1Z ##[group]Run scripts/check.sh build\n",
            f"{step['started_at'][:19]}.2Z ##[endgroup]\n",
            f"{step['completed_at'][:19]}.0Z unexpected end of JSON input\n"]
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def cancelled_guard(self) -> FakeApi:
        """#6624's guard job, as if cancelled while CI still ran."""
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.check(GROUPS[6624][0], "guard", conclusion="cancelled")
        api.responses[f"GET {API}/actions/jobs/{GROUPS[6624][3]}"]["conclusion"] = "cancelled"
        return api

    def test_a_plain_cancellation_is_not_rerun(self):
        for log in ([retry.UNAVAILABLE], None):  # no log; the recorded log, with its JSON line
            with self.subTest(log=log):
                api = self.cancelled_guard()
                if log:
                    api.logs[GROUPS[6624][3]] = log
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_a_job_cancelled_for_running_too_long_is_not_rerun(self):
        timeout = {"message": "The job running on runner GitHub Actions 12 has exceeded the maximum "
                              "execution time of 360 minutes."}
        internal = {"message": "GitHub Actions has encountered an internal error when running your job."}
        key = f"GET {API}/check-runs/{GROUPS[6624][3]}/annotations?per_page=50&page=1"
        for extra in ([], [internal]):
            for cancelled in (True, False):
                with self.subTest(extra=extra, cancelled=cancelled):
                    # The guard's log has "unexpected end of JSON input".
                    api = self.cancelled_guard() if cancelled else FakeApi({6624: entry(6624)})
                    if not cancelled:
                        self.guard_alone(api, 6624)
                    api.responses[key] = [timeout] + extra
                    report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                    self.assertEqual((api.posts(), report.decision), ([], "unknown"))

    def test_every_annotation_is_read(self):
        page = f"GET {API}/check-runs/{GROUPS[6624][3]}/annotations?per_page=50&page={{}}"
        ordinary = [{"message": f"note {i}"} for i in range(50)]
        timeout = {"message": "The action 'Validate' has timed out after 15 minutes."}
        # The recorded guard failure (its JSON line is re-run evidence) with
        # 50 more annotations: re-run if page two is empty...
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.responses[page.format(1)] = ordinary
        api.responses[page.format(2)] = []
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])
        # ...not if it says the step timed out.
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.responses[page.format(1)] = ordinary
        api.responses[page.format(2)] = [timeout]
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn(("GET", page.format(2)[4:]), api.calls)
        # More pages than are read: fail closed.
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        for number in range(1, retry.ANNOTATION_PAGES + 1):
            api.responses[page.format(number)] = ordinary
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), report.decision), ([], "unknown"))
        self.assertIn("too many annotations", summary(report))

    def test_two_eligible_runs_are_both_rerun(self):
        # #6651, had its CI build failed on a 503 too: both runs completed
        # first attempts with transient failures. Each request is made after
        # all reads, so the first one cannot stop the second.
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        api.check(head, "repository integrity", conclusion="success")
        build_job = 137888725562
        job = api.responses[f"GET {API}/actions/jobs/{build_job}"]
        step = next(step for step in job["steps"] if step["conclusion"] == "failure")
        api.logs[build_job] = [f"{step['started_at'][:19]}.1Z ##[group]Run scripts/check.sh build\n",
                               f"{step['started_at'][:19]}.2Z ##[endgroup]\n",
                               f"{step['completed_at'][:19]}.0Z unexpected end of JSON input\n"]
        original_post = api.post
        data = api.responses[f"GET {checks_path(head)}"]

        build = next(c for c in data["check_runs"] if c["name"] == "build")
        successor = build["id"] + 10**6
        api.responses[f"GET {API}/actions/jobs/{successor}"] = {
            "id": successor, "run_id": 45230586597, "run_attempt": 2, "head_sha": head, "name": "build"}

        def post(path):
            # What a re-run does: a new, queued check run for the re-run job.
            if path == RERUN.format(45230586597):
                data["check_runs"].append(dict(build, id=successor, status="queued", conclusion=None))
            return original_post(path)
        api.post = post
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual(api.posts(), [RERUN.format(45230586597), RERUN.format(45230586519)])
        self.assertEqual(report.decision, "retry")

    def two_runs(self) -> tuple[FakeApi, str, dict]:
        """#6651 with a transient build failure too: CI and Bump guard both eligible."""
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        api.check(head, "repository integrity", conclusion="success")
        job = api.responses[f"GET {API}/actions/jobs/137888725562"]
        step = next(step for step in job["steps"] if step["conclusion"] == "failure")
        api.logs[137888725562] = [
            f"{step['started_at'][:19]}.1Z ##[group]Run scripts/check.sh build\n",
            f"{step['started_at'][:19]}.2Z ##[endgroup]\n",
            f"{step['completed_at'][:19]}.0Z unexpected end of JSON input\n"]
        data = api.responses[f"GET {checks_path(head)}"]
        build = next(c for c in data["check_runs"] if c["name"] == "build")
        return api, head, build

    def test_only_the_bots_own_successor_is_accepted(self):
        for case in ("two new runs", "gone", "another run's job", "successor failed"):
            with self.subTest(case=case):
                api, head, build = self.two_runs()
                data = api.responses[f"GET {checks_path(head)}"]
                original_post = api.post

                def post(path, case=case, api=api, data=data, build=build, head=head):
                    if path == RERUN.format(45230586597):
                        data["check_runs"].remove(build)
                        new = [build["id"] + 1, build["id"] + 2] if case == "two new runs" else (
                            [] if case == "gone" else [build["id"] + 1])
                        for check_id in new:
                            conclusion = "failure" if case == "successor failed" else None
                            status = "completed" if conclusion else "queued"
                            data["check_runs"].append(dict(build, id=check_id, status=status,
                                                           conclusion=conclusion))
                            run_id = 1 if case == "another run's job" else 45230586597
                            api.responses[f"GET {API}/actions/jobs/{check_id}"] = {
                                "id": check_id, "run_id": run_id, "run_attempt": 2, "head_sha": head}
                    return original_post(path)
                api.post = post
                report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
                self.assertEqual(api.posts(), [RERUN.format(45230586597)])
                self.assertIn("required checks changed", summary(report))

    def test_a_failed_request_fails_the_job_even_when_the_loop_stops(self):
        api, head, build = self.two_runs()
        original_post = api.post

        def post(path):
            original_post(path)
            api.entries[6651] = None  # the entry leaves the queue
            raise retry.GitHubError(502, f"POST {path}")
        api.post = post
        report = retry.Report(6651, "active")
        with self.assertRaises(retry.GitHubError):
            quiet(retry.triage, api, REPO, 6651, "active", trigger(6651), report)
        self.assertEqual(api.posts(), [RERUN.format(45230586597)])
        self.assertIn("its merge group may be stale", summary(report))

    def test_a_failed_request_does_not_stop_the_others(self):
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        api.check(head, "repository integrity", conclusion="success")
        job = api.responses[f"GET {API}/actions/jobs/137888725562"]
        step = next(step for step in job["steps"] if step["conclusion"] == "failure")
        api.logs[137888725562] = [
            f"{step['started_at'][:19]}.1Z ##[group]Run scripts/check.sh build\n",
            f"{step['started_at'][:19]}.2Z ##[endgroup]\n",
            f"{step['completed_at'][:19]}.0Z unexpected end of JSON input\n"]
        original_post = api.post

        def post(path):
            original_post(path)
            if path == RERUN.format(45230586597):
                raise retry.GitHubError(502, f"POST {path}")
            return 201
        api.post = post
        report = retry.Report(6651, "active")
        with self.assertRaises(retry.GitHubError):
            quiet(retry.triage, api, REPO, 6651, "active", trigger(6651), report)
        self.assertEqual(api.posts(), [RERUN.format(45230586597), RERUN.format(45230586519)])
        self.assertEqual(report.rerun, [45230586519])
        self.assertIn("not repeated", summary(report))

    def test_the_second_rerun_stops_if_the_queue_moves(self):
        for change in ("entry", "attempt", "failure"):
            with self.subTest(change=change):
                api = FakeApi({6651: entry(6651)})
                head = GROUPS[6651][0]
                api.check(head, "repository integrity", conclusion="success")
                job = api.responses[f"GET {API}/actions/jobs/137888725562"]
                step = next(step for step in job["steps"] if step["conclusion"] == "failure")
                api.logs[137888725562] = [
                    f"{step['started_at'][:19]}.1Z ##[group]Run scripts/check.sh build\n",
                    f"{step['started_at'][:19]}.2Z ##[endgroup]\n",
                    f"{step['completed_at'][:19]}.0Z unexpected end of JSON input\n"]
                original_post = api.post

                def post(path, change=change, api=api, head=head):
                    if change == "entry":
                        api.entries[6651] = None  # the entry left the queue
                    elif change == "attempt":
                        api.responses[f"GET {API}/actions/runs/45230586519"]["run_attempt"] = 2
                    else:
                        api.check(head, "source-diagnostics", conclusion="failure")
                    return original_post(path)
                api.post = post
                quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
                self.assertEqual(api.posts(), [RERUN.format(45230586597)])

    def test_a_missing_check_that_appears_pending_does_not_stop_the_rerun(self):
        api = FakeApi({6624: entry(6624)})
        head = GROUPS[6624][0]
        data = api.responses[f"GET {checks_path(head)}"]
        build = next(c for c in data["check_runs"] if c["name"] == "build")
        data["check_runs"].remove(build)  # not reported yet

        def build_starts(path):
            if path == f"{API}/actions/jobs/{GROUPS[6624][3]}" and build not in data["check_runs"]:
                data["check_runs"].append(dict(build, status="in_progress", conclusion=None))
        api.before_get = build_starts
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_a_check_that_passes_while_classifying_does_not(self):
        api = FakeApi({6624: entry(6624)})
        head = GROUPS[6624][0]
        self.guard_alone(api, 6624)

        def build_passes(path):
            if path == f"{API}/actions/jobs/{GROUPS[6624][3]}":
                api.check(head, "build", status="completed", conclusion="success")
        api.before_get = build_passes
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_two_check_runs_for_one_required_check_are_ambiguous(self):
        api = FakeApi({6651: entry(6651)})
        head = GROUPS[6651][0]
        data = api.responses[f"GET {checks_path(head)}"]
        integrity = next(c for c in data["check_runs"] if c["name"] == "repository integrity")
        data["check_runs"].append(dict(integrity, id=max(c["id"] for c in data["check_runs"]) + 1,
                                       conclusion="success"))
        report = quiet(retry.triage, api, REPO, 6651, "active", trigger(6651))
        self.assertEqual((api.posts(), report.decision), ([], "ambiguous"))

    def test_a_check_concluding_otherwise_blocks_the_rerun(self):
        for conclusion in ("action_required", "stale", "startup_failure"):
            with self.subTest(conclusion=conclusion):
                api = FakeApi({6624: entry(6624)})
                self.guard_alone(api, 6624)
                api.check(GROUPS[6624][0], "build", status="completed", conclusion=conclusion)
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual((api.posts(), report.decision), ([], "unknown"))
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.check(GROUPS[6624][0], "build", status="completed", conclusion="neutral")
        quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_entry_that_changes_before_the_rerun_is_left_alone(self):
        api = FakeApi({6624: entry(6624)})

        def move_on(path):
            if path == f"{API}/actions/runs/45239318416" and ("GET", path) in api.calls[:-1]:
                api.entries[6624] = entry(6624, head="b" * 40)  # during the last read of the run
        api.before_get = move_on
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("its merge group may be stale", summary(report))

    def test_run_rerun_by_someone_else_is_left_alone(self):
        api = FakeApi({6624: entry(6624)})

        def rerun_elsewhere(path):
            if path == f"{API}/actions/runs/45239318416" and ("GET", path) in api.calls[:-1]:
                api.responses[f"GET {path}"].update(status="queued", run_attempt=2)
        api.before_get = rerun_elsewhere
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual(api.posts(), [])
        self.assertIn("no longer a completed first attempt", summary(report))

    def test_collision_with_a_passing_entry_ahead_would_be_dequeued_but_is_not(self):
        api = FakeApi({6650: entry(6650)})
        api.before_main_ran(GROUPS[6650][1])  # as at 19:20:39-19:23:27, before #6649 merged
        report = quiet(retry.triage, api, REPO, 6650, "active", trigger(6650))
        self.assertEqual(report.decision, "would-dequeue")
        self.assertIn("**Would dequeue #6650**", summary(report))
        self.assertIn("`Build extension libraries`", summary(report))
        self.assertEqual(api.posts(), [])

    def test_entry_ahead_with_two_check_runs_is_not_attributable(self):
        api = FakeApi({6650: entry(6650)})  # the recorded answer: #6649's checks ran twice
        report = quiet(retry.triage, api, REPO, 6650, "active", trigger(6650))
        self.assertEqual(report.decision, "observe")
        self.assertIn("`build` `ambiguous`", summary(report))

    def test_entry_ahead_still_building_is_not_attributable(self):
        api = FakeApi({6218: entry(6218)})
        api.before_main_ran(GROUPS[6218][1])
        api.check(GROUPS[6218][1], "build", status="in_progress", conclusion=None)  # as at 17:33:16
        report = quiet(retry.triage, api, REPO, 6218, "active", trigger(6218))
        self.assertEqual(report.decision, "observe")
        self.assertIn("Not attributable yet", summary(report))
        self.assertIn("`build` `in_progress`", summary(report))

    def test_front_entry_is_left_to_the_queue(self):
        api = FakeApi({6650: entry(6650, position=1)}, main=GROUPS[6650][1])
        report = quiet(retry.triage, api, REPO, 6650, "dry-run", trigger(6650))
        self.assertIn("front of the queue", summary(report))
        self.assertNotIn(("GET", checks_path(GROUPS[6650][1])), api.calls)

    def test_other_grouping_strategies_get_no_eject_decision(self):
        api = FakeApi({6650: entry(6650)})
        rules = api.responses[f"GET {API}/rules/branches/main?per_page=100&page=1"]
        next(r for r in rules if r["type"] == "merge_queue")["parameters"]["grouping_strategy"] = "HEADGREEN"
        report = quiet(retry.triage, api, REPO, 6650, "active", trigger(6650))
        self.assertEqual(report.decision, "observe")
        self.assertIn("ALLGREEN only", summary(report))

    def rules(self, api: FakeApi) -> list:
        rules = api.responses[f"GET {API}/rules/branches/main?per_page=100&page=1"]
        return next(r for r in rules if r["type"] == "required_status_checks")["parameters"]["required_status_checks"]

    def test_failures_outside_the_required_checks_are_ignored(self):
        # graph sync is not a required check: its failure neither counts nor
        # blocks guard's re-run.
        api = FakeApi({6624: entry(6624)})
        self.guard_alone(api, 6624)
        api.check(GROUPS[6624][0], "graph sync", status="completed", conclusion="failure")
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual([f.check for f in report.failures], ["guard"])
        self.assertEqual(api.posts(), [RERUN.format(45239318416)])

    def test_a_required_check_from_another_app_is_not_this_jobs(self):
        api = FakeApi({6624: entry(6624)})
        next(c for c in self.rules(api) if c["context"] == "guard")["integration_id"] = 99999
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), report.failures), ([], []))
        self.assertIn("still running", summary(report))

    def test_failures_that_are_not_jobs_of_the_required_workflows_block_reruns(self):
        for change in ({"path": ".github/workflows/other.yml"}, {"name": "CI"}, {"event": "push"},
                       {"head_branch": "gh-readonly-queue/main/pr-6624-" + "c" * 40},
                       {"head_repository": {"full_name": "someone/atlas-lean"}}):
            with self.subTest(change=change):
                api = FakeApi({6624: entry(6624)})
                api.responses[f"GET {API}/actions/runs/45239318416"].update(change)
                report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
                self.assertEqual(api.posts(), [])
                self.assertEqual([f.kind for f in report.failures], [retry.UNKNOWN])
        api = FakeApi({6624: entry(6624)})
        api.check(GROUPS[6624][0], "guard", app={"id": 1234, "slug": "other"})
        next(c for c in self.rules(api) if c["context"] == "guard")["integration_id"] = None
        report = quiet(retry.triage, api, REPO, 6624, "active", trigger(6624))
        self.assertEqual((api.posts(), [f.kind for f in report.failures]), ([], [retry.UNKNOWN]))

    def test_untrusted_text_stays_out_of_the_job_output(self):
        api = FakeApi({6624: entry(6624)})
        job = api.responses[f"GET {API}/actions/jobs/137919366370"]
        step = next(step for step in job["steps"] if step["conclusion"] == "failure")
        step["name"] = "Validate | <img src=x> @someone `x`\n::error::forged"
        api.logs[137919366370] = (FIXTURES / "logs" / "137919366370.txt").read_text(
            encoding="utf-8").replace("unexpected end of JSON input", "::add-mask::x unexpected end of JSON input"
                                      ).splitlines(True)
        api.responses[f"GET {API}/actions/runs/45239318416"]["name"] = "Bump guard"
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            report = retry.triage(api, REPO, 6624, "dry-run", trigger(6624))
        self.assertNotIn("::", out.getvalue())
        self.assertNotIn("Validate", out.getvalue())
        row = next(line for line in report.lines if line.startswith("| `guard`"))
        self.assertIn("`Validate / <img src=x> @someone 'x' ::error::forged`", row)
        self.assertEqual(row.count(" | "), 4)


class Main(unittest.TestCase):
    def event(self, **changes) -> dict:
        head, base, run_id, _ = GROUPS[6624]
        run = {"id": run_id, "name": "Bump guard", "path": ".github/workflows/bump-guard.yml",
               "event": "merge_group", "conclusion": "failure", "run_attempt": 1,
               "head_branch": f"gh-readonly-queue/main/pr-6624-{base}", "head_sha": head,
               "repository": {"full_name": REPO}, "head_repository": {"full_name": REPO}}
        run.update(changes)
        return {"workflow_run": run}

    def test_valid_and_invalid_triggers(self):
        found = retry.read_trigger(self.event(), REPO)
        self.assertEqual((found.pr, found.run_id, found.run_attempt), (6624, 45239318416, 1))
        for changes in ({"event": "pull_request"}, {"path": ".github/workflows/evil.yml"}, {"name": "CI"},
                        {"head_branch": "feature"}, {"head_sha": "HEAD"}, {"conclusion": "success"},
                        {"head_repository": {"full_name": "fork/atlas-lean"}}, {"run_attempt": "1"}):
            with self.subTest(changes=changes):
                with self.assertRaises(ValueError):
                    retry.read_trigger(self.event(**changes), REPO)

    def run_main(self, event: dict, pr: str = "6624", switch: str | None = "active",
                 event_name: str = "workflow_run", api: FakeApi | None = None):
        api = api or FakeApi({6624: entry(6624)})
        with tempfile.TemporaryDirectory() as tmp:
            event_path = Path(tmp) / "event.json"
            event_path.write_text(json.dumps(event), encoding="utf-8")
            summary_path = Path(tmp) / "summary.md"
            env = {"GITHUB_REPOSITORY": REPO, "GITHUB_EVENT_NAME": event_name,
                   "GITHUB_EVENT_PATH": str(event_path), "GITHUB_STEP_SUMMARY": str(summary_path),
                   "GH_TOKEN": "token"}
            if switch is not None:
                env["MERGE_QUEUE_RETRY"] = switch
            out = io.StringIO()
            with mock.patch.dict(os.environ, env, clear=False), \
                    mock.patch.object(retry, "Api", return_value=api), contextlib.redirect_stdout(out):
                if switch is None:
                    os.environ.pop("MERGE_QUEUE_RETRY", None)
                try:
                    status = retry.main(["--pr", pr])
                except RuntimeError as error:
                    status = error
            return status, summary_path.read_text(encoding="utf-8"), api, out.getvalue()

    def test_reruns_only_when_the_switch_is_exactly_active(self):
        status, text, api, out = self.run_main(self.event())
        self.assertEqual((status, api.posts()), (0, [RERUN.format(45239318416)]))
        self.assertIn("re-ran the failed jobs of `Bump guard` run 45239318416", text)
        self.assertTrue(re.match(r"::stop-commands::[0-9a-f]{32}\n", out), out[:80])
        for switch in ("ACTIVE", "Active", " active", "true", "", None):
            with self.subTest(switch=switch):
                status, text, api, _ = self.run_main(self.event(), switch=switch)
                self.assertEqual((status, api.posts()), (0, []))
                self.assertIn("Mode: **dry-run**", text)

    def test_other_events_are_dry_runs(self):
        status, text, api, _ = self.run_main({}, event_name="workflow_dispatch")
        self.assertEqual((status, api.posts()), (0, []))

    def test_ineligible_triggers_are_ignored(self):
        for event, pr in ((self.event(path=".github/workflows/evil.yml"), "6624"), (self.event(), "6625")):
            with self.subTest(pr=pr):
                status, text, api, _ = self.run_main(event, pr)
                self.assertEqual((status, api.calls), (0, []))
                self.assertIn("ignoring the triggering run", text)

    def test_the_summary_is_written_when_the_api_fails(self):
        api = FakeApi({6624: entry(6624)})
        api.before_get = mock.Mock(side_effect=RuntimeError("boom"))
        status, text, _, _ = self.run_main(self.event(), api=api)
        self.assertIsInstance(status, RuntimeError)
        self.assertIn("Error, no further action: `boom`", text)


class Workflow(unittest.TestCase):
    """The workflow's trigger, permissions and inputs keep the job safe."""

    @classmethod
    def setUpClass(cls):
        cls.text = WORKFLOW.read_text(encoding="utf-8")

    def test_triggers_on_the_required_check_workflows_only(self):
        names = []
        for path in retry.WORKFLOWS:
            match = re.search(r"^name: (.+)$", (ROOT / path).read_text(encoding="utf-8"), re.M)
            names.append(match.group(1).strip())
        self.assertEqual(names, list(retry.WORKFLOWS.values()))
        self.assertIn(f"    workflows: [{', '.join(names)}]\n", self.text)
        self.assertIn("    types: [completed]\n", self.text)
        self.assertIn('    branches: ["gh-readonly-queue/main/pr-*"]\n', self.text)
        events = re.findall(r"^  ([a-z_]+):$", self.text.split("\non:\n", 1)[1].split("\n\n", 1)[0], re.M)
        self.assertEqual(events, ["workflow_run"])

    def test_select_validates_the_same_workflows_and_ref(self):
        pairs = re.findall(r'^ +"?(\.github/workflows/[a-z-]+\.yml):([^"|]+?)"? *[|)]', self.text, re.M)
        self.assertEqual(dict(pairs), retry.WORKFLOWS)
        self.assertIn(r'"$HEAD_BRANCH" =~ ^gh-readonly-queue/main/pr-([1-9][0-9]{0,6})-[0-9a-f]{40}$', self.text)
        self.assertEqual(retry.QUEUE_BRANCH.pattern, r"gh-readonly-queue/main/pr-([1-9][0-9]{0,6})-([0-9a-f]{40})")
        for check in ('"$RUN_EVENT" != merge_group', '"$RUN_REPOSITORY" != "$GITHUB_REPOSITORY"',
                      '"$HEAD_REPOSITORY" != "$GITHUB_REPOSITORY"', '"$HEAD_SHA" =~ ^[0-9a-f]{40}$'):
            self.assertIn(check, self.text)

    def test_least_privilege_and_trusted_code(self):
        self.assertIn("\npermissions: {}\n", self.text)
        blocks = re.findall(r"^    permissions:\n((?:      .*\n)+)", self.text, re.M)
        self.assertEqual(blocks, ["      actions: write\n      checks: read\n      contents: read\n"
                                  "      pull-requests: read\n      statuses: read\n"])
        self.assertNotIn("secrets.", self.text)
        self.assertEqual(self.text.count("actions/checkout@"), 1)
        checkout = self.text.split("actions/checkout@", 1)[1].split("\n\n", 1)[0]
        self.assertIn("persist-credentials: false", checkout)
        self.assertIn("ref: ${{ github.sha }}", checkout)

    def test_untrusted_values_never_reach_a_script_inline(self):
        scripts = re.findall(r"^ +run: (?:\|\n((?: {10,}.*\n|\n)+)|(.*))", self.text, re.M)
        self.assertEqual(len(scripts), 2)
        for block in scripts:
            self.assertNotIn("${{", "".join(block))

    def test_the_switch_reaches_the_script_unchanged(self):
        self.assertIn("MERGE_QUEUE_RETRY: ${{ vars.MERGE_QUEUE_RETRY }}\n", self.text)
        self.assertEqual(self.text.count("vars."), 1)

    def test_one_job_per_pull_request(self):
        self.assertIn("      group: merge-queue-retry-${{ needs.select.outputs.pr }}\n"
                      "      cancel-in-progress: false\n", self.text)


if __name__ == "__main__":
    unittest.main()
