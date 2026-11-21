#!/usr/bin/env python3
"""The checks `main` requires must keep reporting on PRs and on merge groups.

A PR can be queued only once the required checks pass on it, and the merge
queue then waits for the same checks on each merge group it builds. This test
fails if a required workflow stops being triggered when a PR is opened, updated
or reopened, or when a merge group is built; if its job can be skipped (a
skipped job counts as passing); if the check is renamed or another job reports
the same name; or if a concurrency group is shared across merge groups. The
required checks are the ones listed under "How PRs merge" in CONTRIBUTING.md.

CI runs it in the `repository integrity` job. Locally:

    python3 -m pip install -r scripts/requirements-inventory.txt
    python3 -m unittest discover -s scripts -p test_merge_queue_checks.py
"""

from __future__ import annotations

import copy
import re
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"

# Required check -> (workflow file, the event that reports it on PRs). GitHub
# matches a required check by name: the job's `name`, or its id without one.
REQUIRED = {
    "repository integrity": ("ci.yml", "pull_request"),
    "build": ("ci.yml", "pull_request"),
    "source-diagnostics": ("source-diagnostics.yml", "pull_request"),
    "guard": ("bump-guard.yml", "pull_request_target"),
}
PR_TYPES = {"opened", "synchronize", "reopened"}
FILTERS = {"branches", "branches-ignore", "paths", "paths-ignore"}
# Each merge group has its own ref and commit, so a concurrency group keyed by
# one of these never lets one merge group's run cancel or replace another's.
PER_MERGE_GROUP = ("github.ref", "github.sha", "github.run_id",
                   "github.event.merge_group.head_ref", "github.event.merge_group.head_sha")


def load_workflows() -> dict[str, dict]:
    # BaseLoader keeps the `on` key and reads every value as text.
    return {path.name: yaml.load(path.read_text(encoding="utf-8"), Loader=yaml.BaseLoader)
            for path in sorted(WORKFLOWS.glob("*.y*ml"))}


def documented_checks() -> list[str]:
    text = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
    section = text.split("\n## How PRs merge\n", 1)[1].split("\n## ", 1)[0]
    listing = section.split("\n### Required checks\n", 1)[1].split("\n### ", 1)[0]
    return re.findall(r"^- `([^`]+)`", listing, re.M)


def as_list(value) -> list:
    return [value] if isinstance(value, str) else list(value or [])


def events(workflow: dict) -> dict:
    triggers = workflow.get("on") or {}
    if not isinstance(triggers, dict):
        return {event: {} for event in as_list(triggers)}
    return {event: settings or {} for event, settings in triggers.items()}


def concurrency_group(setting) -> str:
    return setting.get("group", "") if isinstance(setting, dict) else setting or ""


def problems(workflows: dict[str, dict], documented: list[str]) -> list[str]:
    """Every way the required checks could stop reporting; empty when none."""
    found = []
    if documented != list(REQUIRED):
        found.append(f"CONTRIBUTING lists {documented}, not {list(REQUIRED)}")
    reporters: dict[str, list[tuple[str, str]]] = {}
    for name, workflow in workflows.items():
        for job_id, job in (workflow.get("jobs") or {}).items():
            reporters.setdefault(job.get("name", job_id), []).append((name, job_id))
    required_jobs = {(name, job_id) for check, (name, _) in REQUIRED.items()
                     for owner, job_id in reporters.get(check, []) if owner == name}
    for check, (name, pr_event) in REQUIRED.items():
        # Every Actions job reports under the same app, so a second job with
        # this name could satisfy or block the requirement.
        if [owner for owner, _ in reporters.get(check, [])] != [name]:
            found.append(f"{check!r} is reported by {reporters.get(check, [])}, "
                         f"not by one job in {name}")
            continue
        workflow = workflows[name]
        triggers = events(workflow)
        if "merge_group" not in triggers:
            found.append(f"{name} has no merge_group trigger")
        else:
            merge_group = triggers["merge_group"]
            types = as_list(merge_group.get("types", "checks_requested"))
            if set(merge_group) - {"types"} or "checks_requested" not in types:
                found.append(f"{name} filters merge groups: {merge_group}")
        if pr_event not in triggers:
            found.append(f"{name} has no {pr_event} trigger")
        else:
            settings = triggers[pr_event]
            if set(settings) & FILTERS:
                found.append(f"{name} filters PRs: {sorted(set(settings) & FILTERS)}")
            missing = PR_TYPES - set(as_list(settings.get("types", sorted(PR_TYPES))))
            if missing:
                found.append(f"{name} does not run on {pr_event} {sorted(missing)}")
        (_, job_id), = reporters[check]
        job = workflow["jobs"][job_id]
        for key in ("if", "strategy"):
            if key in job:
                found.append(f"{check!r} has a job-level {key!r}")
        # A job whose prerequisite fails is skipped, which counts as passing,
        # so every prerequisite must be required too.
        for prerequisite in as_list(job.get("needs")):
            if (name, prerequisite) not in required_jobs:
                found.append(f"{check!r} needs {prerequisite!r}, which is not required")
        # A new run in a concurrency group cancels the group's pending run even
        # without cancel-in-progress.
        for scope, setting in (("workflow", workflow.get("concurrency")),
                               ("job", job.get("concurrency"))):
            group = concurrency_group(setting)
            if group and not any(key in group for key in PER_MERGE_GROUP):
                found.append(f"{check!r} shares its {scope} concurrency group {group!r} "
                             "across merge groups")
    return found


def put(*path):
    """A change that sets workflows[path[0]]...[path[-2]] to path[-1]."""
    *keys, value = path

    def change(workflows):
        node = workflows
        for key in keys[:-1]:
            if not isinstance(node.get(key), dict):
                node[key] = {}
            node = node[key]
        node[keys[-1]] = value
    return change


def drop(*keys):
    def change(workflows):
        node = workflows
        for key in keys[:-1]:
            node = node[key]
        del node[keys[-1]]
    return change


def rename_job(name, old, new):
    def change(workflows):
        jobs = workflows[name]["jobs"]
        jobs[new] = jobs.pop(old)
    return change


class MergeQueueChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflows = load_workflows()
        cls.documented = documented_checks()

    def check(self, change=None, documented=None):
        workflows = copy.deepcopy(self.workflows)
        if change:
            change(workflows)
        return problems(workflows, self.documented if documented is None else documented)

    def test_required_checks_report_on_every_pr_and_merge_group(self):
        self.assertEqual(self.check(), [])

    def test_equivalent_spellings_pass(self):
        for change in (put("ci.yml", "on", "merge_group", ""),
                       put("ci.yml", "on", "merge_group", {"types": "checks_requested"}),
                       put("ci.yml", "on", "pull_request", "")):
            self.assertEqual(self.check(change), [])

    def test_changes_that_stop_a_check_from_reporting_fail(self):
        cases = {
            "lost merge_group": (drop("ci.yml", "on", "merge_group"), "no merge_group"),
            "list of events": (put("source-diagnostics.yml", "on", ["push", "pull_request"]),
                               "no merge_group"),
            "merge_group branches": (
                put("source-diagnostics.yml", "on", "merge_group", "branches", ["main"]),
                "filters merge groups"),
            "other merge_group type": (
                put("bump-guard.yml", "on", "merge_group", {"types": ["destroyed"]}),
                "filters merge groups"),
            "closed PRs only": (put("ci.yml", "on", "pull_request", {"types": ["closed"]}),
                                "does not run on pull_request"),
            "PR paths": (put("source-diagnostics.yml", "on", "pull_request", "paths", ["docs/**"]),
                         "filters PRs"),
            "lost PR trigger": (drop("bump-guard.yml", "on", "pull_request_target"),
                                "no pull_request_target"),
            "job-level if": (put("ci.yml", "jobs", "build", "if", "github.event_name == 'push'"),
                             "job-level 'if'"),
            "matrix": (put("source-diagnostics.yml", "jobs", "source-diagnostics", "strategy",
                           {"matrix": {"part": ["1", "2"]}}), "job-level 'strategy'"),
            "renamed check": (put("ci.yml", "jobs", "preflight", "name", "integrity"),
                              "'repository integrity' is reported by []"),
            "renamed job id": (rename_job("ci.yml", "build", "lean-build"),
                               "'build' is reported by []"),
            "duplicate name": (put("float-conformance.yml", "jobs", "conformance", "name", "build"),
                               "'build' is reported by"),
            "duplicate job id": (
                put("extra.yml", {"on": {"pull_request": ""}, "jobs": {"guard": {}}}),
                "'guard' is reported by"),
            "prerequisite not required": (
                put("ci.yml", "jobs", "build", "needs", ["preflight", "lint"]), "needs 'lint'"),
            "shared workflow concurrency": (
                put("ci.yml", "concurrency", "group", "${{ github.workflow }}"),
                "workflow concurrency group"),
            "shared job concurrency": (put("ci.yml", "jobs", "build", "concurrency", "lean-build"),
                                       "job concurrency group"),
        }
        for label, (change, message) in cases.items():
            with self.subTest(label):
                found = self.check(change)
                self.assertTrue(any(message in problem for problem in found), found)
        self.assertTrue(self.check(documented=list(REQUIRED)[:-1]))


if __name__ == "__main__":
    unittest.main()
