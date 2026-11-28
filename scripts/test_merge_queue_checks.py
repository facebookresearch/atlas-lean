#!/usr/bin/env python3
"""The checks `main` requires must report on every PR and every merge group.

The merge queue waits for every required check on each merge group it builds.
A required workflow that loses its `merge_group` trigger, skips some PRs with a
filter, skips its job with a job-level `if` (a skipped job counts as passing),
renames the job, or lets one merge group's run cancel another's would leave the
check missing or wrong, and the queue would drop the PR or hold it until its
timeout. The one job-level `if` allowed lets only a pull request skip a job,
and only when the `changes` job of its workflow succeeds and says that the pull
request does not need it (scripts/ci_scope.py); `changes` itself may run on
pull requests only. A required workflow also runs on `pull_request`, never
`pull_request_target`: from 2 December 2026 GitHub blocks `pull_request_target`
runs by default in public repositories, and a required check that never reports
blocks every PR. Merge groups run ci.yml's three required jobs on the 16-core
runner (ci.yml's `build` says why), so a mistyped label there would leave a
merge group's check waiting for a runner that does not exist; actionlint does
not check labels inside an expression. The required checks are the ones listed
under "How PRs merge" in CONTRIBUTING.md.

Run with: python3 -m unittest discover -s scripts -p test_merge_queue_checks.py
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"

# Required check -> the workflow that reports it. GitHub matches a required
# check by name: the job's `name`, or its id when it has none.
REQUIRED = {
    "repository integrity": "ci.yml",
    "build": "ci.yml",
    "check the graph": "ci.yml",
    "source-diagnostics": "source-diagnostics.yml",
    "guard": "bump-guard.yml",
}
PR_EVENTS = ("pull_request",)
FILTERS = {"branches", "branches-ignore", "paths", "paths-ignore", "tags", "tags-ignore"}
# The only job-level `if` a required job may have. A merge group, a push or a
# manual run never asks `changes`; on a pull request, a `changes` job that fails
# or says anything but `false` runs the job too.
SCOPED_IF = re.compile(r"\$\{\{ !cancelled\(\) && \(github\.event_name != 'pull_request' \|\| "
                       r"needs\.changes\.outputs\.([a-z][a-z0-9_-]*) != 'false'\) \}\}")
# Each merge group has its own ref and commit, so a concurrency group keyed by
# one of these never lets one merge group's run cancel another's.
PER_MERGE_GROUP = ("github.ref", "github.sha", "github.run_id",
                   "github.event.merge_group.head_ref", "github.event.merge_group.head_sha")
# The runner of ci.yml's required jobs: 16 cores for merge groups, the standard
# runner for pull requests, pushes and manual runs.
MERGE_GROUP_RUNNER = "${{ github.event_name == 'merge_group' && '16-core-ubuntu' || 'ubuntu-24.04' }}"


def block(lines: list[str], key: str, indent: int) -> list[str] | None:
    """The lines nested under `key:` at `indent` spaces, or None if it is absent."""
    head = re.compile(" " * indent + re.escape(key) + r":(\s.*)?$")
    for index, line in enumerate(lines):
        if head.match(line):
            body = []
            for nested in lines[index + 1:]:
                if nested.strip() and not nested.startswith(" " * (indent + 1)):
                    break
                body.append(nested)
            return body
    return None


def keys(lines: list[str], indent: int) -> list[str]:
    """The mapping keys at exactly `indent` spaces, in order."""
    pattern = re.compile(" " * indent + r"([A-Za-z0-9_-]+):(\s|$)")
    return [match.group(1) for match in map(pattern.match, lines) if match]


def value(lines: list[str], key: str, indent: int) -> str:
    """The text of `key` at `indent` spaces: its inline value and nested lines."""
    pattern = re.compile(" " * indent + re.escape(key) + r":\s*(.*?)\s*$")
    for line in lines:
        match = pattern.match(line)
        if match:
            nested = " ".join(item.strip() for item in block(lines, key, indent))
            return (match.group(1) + " " + nested).strip()
    return ""


def workflow(name: str) -> list[str]:
    text = (WORKFLOWS / name).read_text(encoding="utf-8")
    return [line for line in text.splitlines() if not line.lstrip().startswith("#")]


def jobs(lines: list[str]) -> dict[str, list[str]]:
    section = block(lines, "jobs", 0) or []
    return {job: block(section, job, 2) for job in keys(section, 2)}


def check_name(job: str, body: list[str]) -> str:
    return value(body, "name", 4).strip("'\"") or job


def documented_checks() -> list[str]:
    text = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
    section = text.split("\n## How PRs merge\n", 1)[1].split("\n## ", 1)[0]
    listing = section.split("\n### Required checks\n", 1)[1].split("\n### ", 1)[0]
    return re.findall(r"^- `([^`]+)`", listing, re.M)


class MergeQueueChecks(unittest.TestCase):
    def test_contributing_lists_the_required_checks(self):
        self.assertEqual(documented_checks(), list(REQUIRED))

    def test_merge_groups_run_cis_required_jobs_on_the_16_core_runner(self):
        ci = jobs(workflow("ci.yml"))
        for job in ("preflight", "graph", "build"):
            with self.subTest(job=job):
                self.assertIn(check_name(job, ci[job]), REQUIRED)
                self.assertEqual(value(ci[job], "runs-on", 4), MERGE_GROUP_RUNNER)

    def test_the_graph_job_runs_the_graph_check(self):
        body = " ".join(jobs(workflow("ci.yml"))["graph"])
        self.assertIn("autoform check blueprint --lean-root .", body)

    def test_required_workflows_run_on_every_pr_and_every_merge_group(self):
        for name in sorted(set(REQUIRED.values())):
            with self.subTest(workflow=name):
                lines = workflow(name)
                events = block(lines, "on", 0)
                self.assertIsNotNone(events, "no top-level `on:` block")
                self.assertIn("merge_group", keys(events, 2))
                # Only the activity type is named: a branch filter would skip
                # some merge groups without reporting the check.
                self.assertEqual(value(events, "merge_group", 2), "types: [checks_requested]")
                triggers = [event for event in PR_EVENTS if event in keys(events, 2)]
                self.assertTrue(triggers, "no pull request trigger")
                self.assertNotIn("pull_request_target", keys(events, 2),
                                 "pull_request_target is blocked by default from 2 December 2026")
                for event in triggers:
                    filters = FILTERS & set(keys(block(events, event, 2), 4))
                    self.assertFalse(filters, f"{event} filters skip some PRs: {filters}")
                # A new run in a concurrency group cancels the group's pending
                # run even without cancel-in-progress.
                concurrency = [line for line in block(lines, "concurrency", 0) or []
                               if line.strip()]
                group = value(concurrency, "group", 2) if concurrency else value(
                    lines, "concurrency", 0)
                if group:
                    self.assertTrue(any(key in group for key in PER_MERGE_GROUP),
                                    f"merge groups could cancel each other: {group}")

    def test_each_required_check_has_one_job_that_only_a_pull_request_can_skip(self):
        owners: dict[str, list[tuple[str, str, list[str]]]] = {}
        for path in sorted(WORKFLOWS.glob("*.y*ml")):
            for job, body in jobs(workflow(path.name)).items():
                owners.setdefault(check_name(job, body), []).append((path.name, job, body))
        required_jobs = {(name, job) for check, name in REQUIRED.items()
                         for path, job, _ in owners.get(check, []) if path == name}
        for check, name in REQUIRED.items():
            with self.subTest(check=check):
                # Every Actions job reports under the same app, so a second
                # job with this name could satisfy or block the requirement.
                found = owners.get(check, [])
                self.assertEqual([path for path, _, _ in found], [name],
                                 f"exactly one job, in {name}, must report {check!r}")
                _, job, body = found[0]
                self.assertIsNone(block(body, "strategy", 4), f"job {job} has a job-level strategy")
                prerequisites = re.findall(r"[A-Za-z0-9_-]+", value(body, "needs", 4))
                condition = SCOPED_IF.fullmatch(value(body, "if", 4))
                if block(body, "if", 4) is not None:
                    self.assertIsNotNone(condition, f"job {job} has another job-level if")
                # A job whose prerequisite fails is skipped, which counts as
                # passing, so every prerequisite must be required too, except
                # `changes`, whose failure the condition above runs the job on.
                for prerequisite in prerequisites:
                    if prerequisite != "changes":
                        self.assertIn((name, prerequisite), required_jobs,
                                      f"{job} needs {prerequisite}, which is not required")
                if "changes" not in prerequisites:
                    self.assertIsNone(condition, f"job {job} reads changes without needing it")
                    continue
                self.assertIsNotNone(condition, f"job {job} needs changes without the condition above")
                changes = jobs(workflow(name)).get("changes")
                self.assertIsNotNone(changes, f"{name} has no changes job")
                for key in ("strategy", "needs"):
                    self.assertIsNone(block(changes, key, 4), f"job changes has a job-level {key}")
                # It may skip itself outside pull requests, which alone consult it, and nothing more.
                if block(changes, "if", 4) is not None:
                    self.assertIn(value(changes, "if", 4), ("github.event_name == 'pull_request'",
                                                            "${{ github.event_name == 'pull_request' }}"))
                self.assertNotIn(check_name("changes", changes), REQUIRED)
                self.assertIn(condition.group(1), keys(block(changes, "outputs", 4) or [], 6),
                              f"job changes has no output {condition.group(1)}")


if __name__ == "__main__":
    unittest.main()
