#!/usr/bin/env python3
"""The checks `main` requires must keep reporting on PRs and on merge groups.

A PR can be queued only once the required checks pass on it, and the merge
queue then waits for the same checks on each merge group it builds. This test
catches accidental workflow changes that would stop a required check from
reporting, or let it pass without running. It fails if a required workflow:

- loses its trigger for PRs (opened, updated, reopened) or for merge groups,
  or filters some of them out;
- runs on pushes to anything but the `main` branch, or on another event that
  could report the same checks on a PR's head commit (such as
  `pull_request_target`). A push to a PR's branch, or of a tag on a PR's head,
  would report them there for a tree other than the merge;
- loses or renames the job that reports a check, or another job in any
  workflow reports the same name (a matrix job's name includes its matrix
  values);
- can skip that job, which counts as passing: a job-level `if`, a matrix, a
  reusable workflow, a prerequisite that is not required itself, or
  `continue-on-error`;
- loses the step that runs the check's entry point, or lets that step be
  skipped or its failure ignored;
- uses a concurrency group that is not specific to each run's ref or commit,
  so that one merge group's run could cancel another's.

Both `repository integrity` and `source-diagnostics` must also run this test,
each in a step that is exactly its command, so that a change that makes one
workflow skip its jobs is still caught by the other.

This test is not a security boundary: it catches accidental changes, and a
deliberately misleading workflow change is for human review to catch. The
required checks are the ones listed under "How PRs merge" in CONTRIBUTING.md.
Locally:

    python3 -m pip install -r scripts/requirements-inventory.txt
    python3 -m unittest discover -s scripts -p test_merge_queue_checks.py
"""

from __future__ import annotations

import copy
import itertools
import re
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"

# Required check -> the workflow that reports it. GitHub matches a required
# check by the job's `name`, or its id when it has none.
REQUIRED = {
    "repository integrity": "ci.yml",
    "build": "ci.yml",
    "source-diagnostics": "source-diagnostics.yml",
}
# The step each required job must have, running its check.
ENTRY_POINTS = {
    "repository integrity": "scripts/check.sh preflight",
    "build": "scripts/check.sh build",
    "source-diagnostics": "scripts/run_source_diagnostics.sh",
}
RUN_THIS_TEST = ("repository integrity", "source-diagnostics")
COMMAND = ('"$RUNNER_TEMP/merge-queue-venv/bin/python" -m unittest discover '
           "-s scripts -p test_merge_queue_checks.py -v")
PR_TYPES = {"opened", "synchronize", "reopened"}
FILTERS = {"branches", "branches-ignore", "paths", "paths-ignore", "tags", "tags-ignore"}
# Each merge group has its own ref and commit, so a concurrency group keyed by
# one of these never lets one merge group's run cancel another's.
PER_MERGE_GROUP = ("github.ref", "github.sha", "github.run_id",
                   "github.event.merge_group.head_ref", "github.event.merge_group.head_sha")
# Events a required workflow may also run on. Checks from workflow_dispatch and
# schedule runs never satisfy a branch ruleset's required checks (GitHub Docs,
# "Troubleshooting required status checks").
OTHER_EVENTS = {"push", "merge_group", "workflow_dispatch", "schedule"}


def load_workflows() -> dict[str, dict]:
    # BaseLoader keeps `on` a string key and every scalar a string.
    return {path.name: yaml.load(path.read_text(encoding="utf-8"), Loader=yaml.BaseLoader)
            for path in sorted(WORKFLOWS.glob("*.y*ml"))}


def documented_checks() -> list[str]:
    text = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
    section = text.split("\n## How PRs merge\n", 1)[1].split("\n## ", 1)[0]
    listing = section.split("\n### Required checks\n", 1)[1].split("\n### ", 1)[0]
    return re.findall(r"^- `([^`]+)`", listing, re.M)


def as_list(value) -> list:
    return value if isinstance(value, list) else [] if value in (None, "") else [value]


def events(workflow: dict) -> dict[str, dict]:
    """The workflow's triggers, each with its settings."""
    triggers = workflow.get("on")
    if not isinstance(triggers, dict):
        return {event: {} for event in as_list(triggers)}
    return {event: settings if isinstance(settings, dict) else {}
            for event, settings in triggers.items()}


def is_false(value) -> bool:
    return (value in (None, "false", "False", "FALSE")
            or re.fullmatch(r"\$\{\{\s*false\s*\}\}", str(value)) is not None)


def runs(step, command: str) -> bool:
    """Whether a step runs exactly this one command (comment lines aside),
    unconditionally, with its failure not ignored."""
    if not isinstance(step, dict) or "if" in step or not is_false(step.get("continue-on-error")):
        return False
    lines = [line.strip() for line in str(step.get("run", "")).splitlines()]
    lines = [line for line in lines if line and not line.startswith("#")]
    return len(lines) == 1 and " ".join(lines[0].split()) in (command, "./" + command)


def check_names(job_id: str, job) -> list[str]:
    """The names a job's checks report: its `name`, or its id, with a literal
    matrix substituted for `${{ matrix.<key> }}` or, when the name does not use
    the matrix, appended in parentheses."""
    if not isinstance(job, dict):
        return [job_id]
    name = str(job.get("name", job_id))
    strategy = job.get("strategy")
    matrix = strategy.get("matrix") if isinstance(strategy, dict) else None
    if not isinstance(matrix, dict):
        return [name]
    axes = {key: values for key, values in matrix.items()
            if key not in ("include", "exclude") and isinstance(values, list)}
    combos = [dict(zip(axes, values))
              for values in itertools.product(*axes.values())] if axes else []
    combos += [entry for entry in as_list(matrix.get("include")) if isinstance(entry, dict)]
    used = re.findall(r"\$\{\{\s*matrix\.([\w-]+)\s*\}\}", name)
    if not used:
        return [f"{name} ({', '.join(map(str, combo.values()))})" for combo in combos] or [name]
    return [re.sub(r"\$\{\{\s*matrix\.([\w-]+)\s*\}\}",
                   lambda match: str(combo.get(match.group(1), "")), name) for combo in combos]


def concurrency_group(setting) -> str:
    if isinstance(setting, dict):
        return str(setting.get("group", ""))
    return "" if setting in (None, "") else str(setting)


def problems(workflows: dict[str, dict], documented: list[str]) -> list[str]:
    """Every way the required checks could stop reporting; empty when none."""
    found = []
    if documented != list(REQUIRED):
        found.append(f"CONTRIBUTING lists {documented}, not {list(REQUIRED)}")
    # Every Actions job reports under the same app, so a second job with a
    # required check's name could satisfy or block the requirement.
    reporters: dict[str, list[tuple[str, str]]] = {}
    for name, workflow in workflows.items():
        for job_id, job in (workflow.get("jobs") or {}).items():
            for title in check_names(job_id, job):
                if title in REQUIRED:
                    reporters.setdefault(title, []).append((name, job_id))
    required_jobs = {reporter for check, name in REQUIRED.items()
                     for reporter in reporters.get(check, []) if reporter[0] == name}
    for check, name in REQUIRED.items():
        if [owner for owner, _ in reporters.get(check, [])] != [name]:
            found.append(f"{check!r} is reported by {reporters.get(check, [])}, "
                         f"not by one job in {name}")
            continue
        workflow = workflows[name]
        triggers = events(workflow)
        merge_group = triggers.get("merge_group")
        if merge_group is None:
            found.append(f"{name} has no merge_group trigger")
        elif set(merge_group) - {"types"} or "checks_requested" not in as_list(
                merge_group.get("types", "checks_requested")):
            found.append(f"{name} filters merge groups: {merge_group}")
        pull_request = triggers.get("pull_request")
        if pull_request is None:
            found.append(f"{name} has no pull_request trigger")
        elif set(pull_request) & FILTERS or PR_TYPES - set(
                as_list(pull_request.get("types", sorted(PR_TYPES)))):
            found.append(f"{name} filters PRs: {pull_request}")
        push = triggers.get("push")
        if push is not None and (set(as_list(push.get("branches"))) != {"main"}
                                 or {"branches-ignore", "tags", "tags-ignore"} & set(push)):
            found.append(f"{name} runs on pushes to refs other than the main branch")
        extra = sorted(set(triggers) - OTHER_EVENTS - {"pull_request"})
        if extra:
            found.append(f"{name} also runs on {extra}, which could report its checks "
                         "on a PR's head for another tree")
        (_, job_id), = reporters[check]
        job = workflow["jobs"][job_id]
        for key in ("if", "uses"):
            if key in job:
                found.append(f"{check!r} has a job-level {key!r}")
        strategy = job.get("strategy")
        if strategy is not None and not (isinstance(strategy, dict) and "matrix" not in strategy):
            found.append(f"{check!r} has a job-level matrix")
        # A new run in a concurrency group cancels the group's pending run even
        # without cancel-in-progress.
        for setting in (workflow.get("concurrency"), job.get("concurrency")):
            group = concurrency_group(setting)
            if group and not any(key in group for key in PER_MERGE_GROUP):
                found.append(f"{name} concurrency group {group!r} could let one merge group's "
                             "run cancel another's")
        if not is_false(job.get("continue-on-error")):
            found.append(f"{check!r} has a job-level continue-on-error")
        # A job whose prerequisite is skipped is skipped too, which counts as
        # passing, so every prerequisite must be required itself.
        for prerequisite in as_list(job.get("needs")):
            if (name, prerequisite) not in required_jobs:
                found.append(f"{check!r} needs {prerequisite!r}, which is not required")
        steps = as_list(job.get("steps"))
        if not any(runs(step, ENTRY_POINTS[check]) for step in steps):
            found.append(f"{check!r} has no step that is exactly {ENTRY_POINTS[check]!r}")
        if check in RUN_THIS_TEST and not any(runs(step, COMMAND) for step in steps):
            found.append(f"{check!r} has no step that is exactly {COMMAND!r}")
    return found


FIXTURE = {
    "ci.yml": {
        "name": "CI",
        "on": {"push": {"branches": ["main"]},
               "pull_request": {"types": ["opened", "synchronize", "reopened"]},
               "merge_group": {"types": ["checks_requested"]}},
        "concurrency": {"group": "${{ github.workflow }}-${{ github.ref }}"},
        "jobs": {"preflight": {"name": "repository integrity",
                               "steps": [{"run": "scripts/check.sh preflight"},
                                         {"run": "pip install"}, {"run": COMMAND}]},
                 "build": {"needs": "preflight", "steps": [
                     {"uses": "actions/checkout@v7"},
                     {"name": "Build", "run": "scripts/check.sh build"},
                     {"if": "github.ref == 'refs/heads/main'", "uses": "actions/cache/save@v5"}]}},
    },
    "source-diagnostics.yml": {
        "name": "Source diagnostics",
        "on": {"push": {"branches": "main"}, "pull_request": "", "merge_group": ""},
        "jobs": {"source-diagnostics": {"steps": [
            {"run": COMMAND.replace(" -s", "  -s") + "\n"},
            {"id": "diagnostics", "run": "scripts/run_source_diagnostics.sh"}]}},
    },
    "bump-guard.yml": {
        "name": "Bump guard",
        "on": {"pull_request_target": "", "merge_group": ""},
        "jobs": {"guard": {}},
    },
}


def put(*path):
    """A change that sets FIXTURE[path[0]]...[path[-2]] to path[-1]."""
    *keys, value = path

    def change(workflows):
        node = workflows
        for key in keys[:-1]:
            if not isinstance(node.get(key), dict):
                node[key] = {}
            node = node[key]
        node[keys[-1]] = value
    return change


def drop(*path):
    """A change that removes FIXTURE[path[0]]...[path[-1]]."""
    def change(workflows):
        node = workflows
        for key in path[:-1]:
            node = node[key]
        del node[path[-1]]
    return change


class MergeQueueChecks(unittest.TestCase):
    def check(self, change=None, documented=None):
        workflows = copy.deepcopy(FIXTURE)
        if change:
            change(workflows)
        return problems(workflows, list(REQUIRED) if documented is None else documented)

    def test_live_workflows_report_every_required_check(self):
        self.assertEqual(problems(load_workflows(), documented_checks()), [])

    def test_equivalent_spellings_pass(self):
        for change in (None,
                       put("ci.yml", "jobs", "build", "name", "build"),
                       put("ci.yml", "on", "push", {"branches": "main", "paths": ["**.lean"]}),
                       put("ci.yml", "on", "merge_group", {"types": "checks_requested"}),
                       put("ci.yml", "on", "workflow_dispatch", ""),
                       put("ci.yml", "jobs", "build", "continue-on-error", "false"),
                       put("source-diagnostics.yml", "on",
                           ["pull_request", "merge_group", "workflow_dispatch"]),
                       put("ci.yml", "jobs", "build", "strategy", {"fail-fast": "false"}),
                       put("ci.yml", "jobs", "build", "steps",
                           [{"run": "./scripts/check.sh build"}]),
                       put("ci.yml", "jobs", "build", "steps",
                           [{"continue-on-error": "${{ false }}",
                             "run": "# Build every library.\nscripts/check.sh build\n"}]),
                       put("bump-guard.yml", "jobs", "build",
                           {"strategy": {"matrix": {"cc": ["gcc", "clang"]}}})):
            with self.subTest(change):
                self.assertEqual(self.check(change), [])

    def test_changes_that_stop_a_check_from_reporting_fail(self):
        build_steps = ("ci.yml", "jobs", "build", "steps")
        cases = {
            "merge_group dropped": (drop("ci.yml", "on", "merge_group"),
                                    "no merge_group trigger"),
            "merge groups filtered": (
                put("ci.yml", "on", "merge_group", {"branches": ["main"]}),
                "filters merge groups"),
            "pull_request dropped": (drop("source-diagnostics.yml", "on", "pull_request"),
                                     "no pull_request trigger"),
            "PR updates skipped": (
                put("ci.yml", "on", "pull_request", {"types": ["opened", "reopened"]}),
                "filters PRs"),
            "PRs filtered by path": (
                put("ci.yml", "on", "pull_request", {"paths": ["**.lean"]}), "filters PRs"),
            "push on every branch": (put("ci.yml", "on", "push", ""),
                                     "refs other than the main branch"),
            "push on release branches too": (
                put("ci.yml", "on", "push", {"branches": ["main", "release/*"]}),
                "refs other than the main branch"),
            "push of tags": (put("ci.yml", "on", "push", {"branches": ["main"], "tags": ["v*"]}),
                             "refs other than the main branch"),
            "pull_request_target added": (put("ci.yml", "on", "pull_request_target", ""),
                                          "also runs on ['pull_request_target']"),
            "build renamed": (put("ci.yml", "jobs", "build", "name", "Build"),
                              "'build' is reported by []"),
            "another workflow's job named build": (
                put("bump-guard.yml", "jobs", "build", {}), "'build' is reported by"),
            "Source diagnostics' job dropped": (
                put("source-diagnostics.yml", "jobs", {}), "'source-diagnostics' is reported by"),
            "job-level if": (put("ci.yml", "jobs", "build", "if", "github.event_name == 'push'"),
                             "job-level 'if'"),
            "matrix, which renames the check": (
                put("ci.yml", "jobs", "build", "strategy", {"matrix": {"os": ["ubuntu-24.04"]}}),
                "'build' is reported by []"),
            "matrix keeping the check's name": (
                lambda workflows: (
                    put("ci.yml", "jobs", "build", "name", "${{ matrix.check }}")(workflows),
                    put("ci.yml", "jobs", "build", "strategy",
                        {"matrix": {"check": ["build"]}})(workflows)),
                "job-level matrix"),
            "an advisory matrix job reporting build": (
                put("bump-guard.yml", "jobs", "phases",
                    {"name": "${{ matrix.phase }}",
                     "strategy": {"matrix": {"phase": ["build", "test"]}}}),
                "'build' is reported by"),
            "a constant concurrency group": (put("ci.yml", "concurrency", {"group": "ci"}),
                                             "could let one merge group's run cancel"),
            "a group keyed only by the PR": (
                put("source-diagnostics.yml", "concurrency",
                    "diagnostics-${{ github.event.pull_request.number }}"),
                "could let one merge group's run cancel"),
            "reusable workflow": (
                put("ci.yml", "jobs", "build", "uses", "./.github/workflows/b.yml"),
                "job-level 'uses'"),
            "job-level continue-on-error": (
                put("ci.yml", "jobs", "build", "continue-on-error", "true"),
                "job-level continue-on-error"),
            "prerequisite that is not required": (
                put("ci.yml", "jobs", "build", "needs", ["preflight", "docs"]),
                "needs 'docs', which is not required"),
            "build step dropped": (put(*build_steps, [{"uses": "actions/checkout@v7"}]),
                                   "no step that is exactly 'scripts/check.sh build'"),
            "build step made conditional": (
                put(*build_steps, [{"if": "github.event_name == 'push'",
                                    "run": "scripts/check.sh build"}]),
                "no step that is exactly 'scripts/check.sh build'"),
            "build step failure ignored": (
                put(*build_steps, [{"continue-on-error": "true",
                                    "run": "scripts/check.sh build"}]),
                "no step that is exactly 'scripts/check.sh build'"),
            "build command changed": (
                put(*build_steps, [{"run": "scripts/check.sh build || true"}]),
                "no step that is exactly 'scripts/check.sh build'"),
            "diagnostics step dropped": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": COMMAND}]),
                "no step that is exactly 'scripts/run_source_diagnostics.sh'"),
            "this test dropped from Source diagnostics": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": "scripts/run_source_diagnostics.sh"}]),
                "'source-diagnostics' has no step that is exactly"),
            "this test made conditional in CI": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"run": "scripts/check.sh preflight"},
                     {"if": "github.event_name == 'push'", "run": COMMAND}]),
                "'repository integrity' has no step that is exactly"),
        }
        for label, (change, message) in cases.items():
            with self.subTest(label):
                found = self.check(change)
                self.assertTrue(any(message in problem for problem in found), found)
        self.assertTrue(self.check(documented=list(REQUIRED)[:-1]))


if __name__ == "__main__":
    unittest.main()
