#!/usr/bin/env python3
"""The checks `main` requires must keep reporting on PRs and on merge groups.

A PR can be queued only once the required checks pass on it, and the merge
queue then waits for the same checks on each merge group it builds. This test
fails if a required workflow:

- loses its trigger for PRs (opened, updated, reopened) or for merge groups,
  or filters some of them out;
- can skip the job that reports the check (a skipped job counts as passing):
  a job-level `if`, a matrix, or a prerequisite that is not required itself;
- renames the check, puts an expression in the job's name, lets another job
  report (or possibly report, through an expression in its name) the same
  name, or moves the job into a reusable workflow (which reports
  `caller / callee` instead);
- uses a concurrency group other than the forms below, which are known to
  differ between any two PRs and any two merge groups, or one that another
  workflow's group could match: GitHub concurrency groups are repository-wide
  and case-insensitive, so one run could cancel or replace another's. In a
  reusable workflow, `github.workflow` is the caller's name;
- runs on pushes to any branch but `main`. A push to a PR's branch would report
  the same checks on the PR's head commit for another tree, and a push to one
  of the queue's `gh-readonly-queue/...` branches, which GitHub creates for
  each merge group, would report them on the merge group's commit and could
  share its concurrency group.

It also fails if a required workflow gains another event that could report
the same checks on a PR's head (such as `pull_request_target`), or unless both
`repository integrity` and `source-diagnostics` have a step that is exactly
the command that runs this whole test, with no condition, so that a change
that makes one workflow skip its jobs is still caught by the other.

The required checks are the ones listed under "How PRs merge" in
CONTRIBUTING.md. Locally:

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
# The bump guard's `guard` is not required: its PR event, pull_request_target,
# is blocked by default in public repositories unless an Actions event policy
# allows it, and a required check that never runs blocks every PR.
REQUIRED = {
    "repository integrity": ("ci.yml", "pull_request"),
    "build": ("ci.yml", "pull_request"),
    "source-diagnostics": ("source-diagnostics.yml", "pull_request"),
}
PR_TYPES = {"opened", "synchronize", "reopened"}
FILTERS = {"branches", "branches-ignore", "paths", "paths-ignore"}
# The checks whose jobs run this test, and the whole `run` of the step that
# does it: an earlier step installs PyYAML into that virtual environment.
RUN_THIS_TEST = ("repository integrity", "source-diagnostics")
COMMAND = ('"$RUNNER_TEMP/merge-queue-venv/bin/python" -m unittest discover '
           "-s scripts -p test_merge_queue_checks.py -v")
STEP_KEYS = {"name", "id", "env", "run", "timeout-minutes"}
# Events a required workflow may run on besides its PR event. Pushes must be
# limited to `main`; a workflow_dispatch run reports on a PR's head only if a
# maintainer starts it on that branch.
OTHER_EVENTS = {"push", "merge_group", "workflow_dispatch", "schedule"}
# Concurrency groups known to differ between any two runs of the PR event and
# between any two merge groups. Both start with the workflow's name. Under
# pull_request_target, github.ref is the default branch for every PR, so the
# second form is needed there.
SAFE_GROUPS = {
    "pull_request": {"${{ github.workflow }}-${{ github.ref }}"},
    "pull_request_target": {
        "${{ github.workflow }}-${{ github.event.merge_group.head_ref || "
        "github.event.pull_request.number }}",
    },
}


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


def normalised(group: str) -> str:
    return re.sub(r"\$\{\{\s*(.*?)\s*\}\}",
                  lambda m: "${{ " + " ".join(m.group(1).split()) + " }}", group.strip())


def concurrency_group(setting) -> str:
    return (setting.get("group", "") if isinstance(setting, dict) else setting) or ""


def literal_start(workflow_name: str | None, group: str) -> str:
    """The text a group always starts with, case-folded, after expanding a
    leading `${{ github.workflow }}`; empty if an expression comes first. In a
    reusable workflow, github.workflow is the caller's name, so pass None.
    github.ref is always a full ref, so it starts with `refs/`."""
    group = normalised(group)
    lead = "${{ github.workflow }}"
    if group.startswith(lead) and workflow_name is not None:
        group = workflow_name + group[len(lead):]
    head, _, tail = group.partition("${{")
    if ("${{" + tail).startswith("${{ github.ref }}"):
        head += "refs/"
    return head.casefold()


def pushes_to_other_branches(push: dict) -> bool:
    """Whether a push trigger can run for a branch other than `main`. A filter
    on tags alone does not run for branches."""
    if "branches" in push:
        return set(as_list(push["branches"])) != {"main"}
    return "branches-ignore" in push or not ({"tags", "tags-ignore"} & set(push))


def may_be_named(name: str, check: str) -> bool:
    """Whether a job name, possibly with expressions, can render as `check`."""
    if "${{" not in name:
        return name == check
    prefix, suffix = name.split("${{", 1)[0], name.rsplit("}}", 1)[-1]
    return (check.startswith(prefix) and check.endswith(suffix)
            and len(check) >= len(prefix) + len(suffix))


def runs_this_test(step) -> bool:
    run = str(step.get("run", "")).strip() if isinstance(step, dict) else ""
    return (set(step or {}) <= STEP_KEYS and "\n" not in run
            and " ".join(run.split()) == COMMAND)


def problems(workflows: dict[str, dict], documented: list[str]) -> list[str]:
    """Every way the required checks could stop reporting; empty when none."""
    found = []
    if documented != list(REQUIRED):
        found.append(f"CONTRIBUTING lists {documented}, not {list(REQUIRED)}")
    names: dict[str, list[str]] = {}
    for name, workflow in workflows.items():
        names.setdefault(str(workflow.get("name", name)).casefold(), []).append(name)
    for title, files in names.items():
        if len(files) > 1:
            found.append(f"workflows {files} share the name {title!r}, so their "
                         "concurrency groups can collide")
    # A required check needs one job whose name is exactly the check; a job
    # whose name holds an expression that could render as it is a second one.
    reporters: dict[str, list[tuple[str, str]]] = {}
    for name, workflow in workflows.items():
        for job_id, job in (workflow.get("jobs") or {}).items():
            for check in REQUIRED:
                if may_be_named(job.get("name", job_id), check):
                    reporters.setdefault(check, []).append((name, job_id))
    groups = [(name, None if "workflow_call" in events(workflow)
               else str(workflow.get("name", name)), scope, concurrency_group(setting))
              for name, workflow in workflows.items()
              for scope, setting in [("workflow", workflow.get("concurrency"))] + [
                  (f"job {job_id}", job.get("concurrency"))
                  for job_id, job in (workflow.get("jobs") or {}).items()]
              if concurrency_group(setting)]
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
        if "push" in triggers and pushes_to_other_branches(triggers["push"]):
            found.append(f"{name} runs on pushes to branches other than main")
        extra = sorted(set(triggers) - OTHER_EVENTS - {pr_event})
        if extra:
            found.append(f"{name} also runs on {extra}, which could report its checks "
                         "for another tree")
        (_, job_id), = reporters[check]
        job = workflow["jobs"][job_id]
        if "${{" in job.get("name", ""):
            found.append(f"{check!r} has an expression in its job name, so it may report "
                         "another name on some events")
        for key in ("if", "strategy", "uses"):
            if key in job:
                found.append(f"{check!r} has a job-level {key!r}")
        for prerequisite in as_list(job.get("needs")):
            if (name, prerequisite) not in required_jobs:
                found.append(f"{check!r} needs {prerequisite!r}, which is not required")
        # A new run in a concurrency group cancels the group's pending run even
        # without cancel-in-progress.
        group = concurrency_group(workflow.get("concurrency"))
        if group:
            if normalised(group) not in SAFE_GROUPS[pr_event]:
                found.append(f"{name} concurrency group {group!r} is not one of the forms "
                             f"known to differ per {pr_event} and per merge group")
            start = literal_start(str(workflow.get("name", name)), group)
            for owner, title, scope, other in groups:
                if (owner, scope) == (name, "workflow"):
                    continue
                other_start = literal_start(title, other)
                if not other_start or other_start.startswith(start) or start.startswith(
                        other_start):
                    found.append(f"{owner} {scope} concurrency group {other!r} could match "
                                 f"{name}'s {group!r}")
        if job.get("concurrency"):
            found.append(f"{check!r} has a job-level concurrency group, which is unverified")
        if check in RUN_THIS_TEST and not any(map(runs_this_test, as_list(job.get("steps")))):
            found.append(f"{check!r} has no step that is exactly {COMMAND!r}")
    return found


# A minimal configuration that passes, for the checker's own tests below; the
# live workflows are checked separately.
FIXTURE = {
    "ci.yml": {
        "name": "CI",
        "on": {"push": {"branches": ["main"]},
               "pull_request": {"types": ["opened", "synchronize", "reopened"]},
               "merge_group": {"types": ["checks_requested"]}},
        "concurrency": {"group": "${{ github.workflow }}-${{ github.ref }}"},
        "jobs": {"preflight": {"name": "repository integrity",
                               "steps": [{"run": "pip install"}, {"run": COMMAND}]},
                 "build": {"needs": "preflight"}},
    },
    "source-diagnostics.yml": {
        "name": "Source diagnostics",
        "on": {"push": {"branches": "main"}, "pull_request": "", "merge_group": ""},
        "jobs": {"source-diagnostics": {"steps": [
            {"uses": "actions/checkout"},
            {"name": "Test", "run": COMMAND.replace(" -s", "  -s") + "\n"}]}},
    },
    "bump-guard.yml": {
        "name": "Bump guard",
        "on": {"pull_request_target": "", "merge_group": ""},
        "jobs": {"guard": {}},
    },
    "lint.yml": {"on": {"pull_request": {"paths": ["docs/**"]}},
                 "concurrency": {"group": "lint-${{ github.ref }}"}, "jobs": {"lint": {}}},
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
    def check(self, change=None, documented=None):
        workflows = copy.deepcopy(FIXTURE)
        if change:
            change(workflows)
        return problems(workflows, list(REQUIRED) if documented is None else documented)

    def test_live_workflows_report_every_required_check(self):
        self.assertEqual(problems(load_workflows(), documented_checks()), [])

    def test_equivalent_spellings_pass(self):
        for change in (None,
                       put("ci.yml", "on", "merge_group", ""),
                       put("ci.yml", "on", "merge_group", {"types": "checks_requested"}),
                       put("ci.yml", "on", "pull_request", ""),
                       put("ci.yml", "jobs", "build", "name", "build"),
                       put("ci.yml", "concurrency", "group",
                           "${{github.workflow}}-${{  github.ref }}"),
                       put("ci.yml", "on", "push", {"branches": "main"}),
                       put("ci.yml", "on", "push", {"tags": ["v*"]}),
                       put("nightly.yml", {"name": "CI-nightly", "on": {"schedule": ""},
                                           "concurrency": {"group": "${{ github.workflow }}-"
                                                                    "${{ github.ref }}"},
                                           "jobs": {"nightly": {}}})):
            with self.subTest(change):
                self.assertEqual(self.check(change), [])

    def test_changes_that_stop_a_check_from_reporting_fail(self):
        cases = {
            "lost merge_group": (drop("ci.yml", "on", "merge_group"), "no merge_group"),
            "list of events": (put("source-diagnostics.yml", "on", ["pull_request"]),
                               "no merge_group"),
            "merge_group branches": (
                put("source-diagnostics.yml", "on", "merge_group", "branches", ["main"]),
                "filters merge groups"),
            "other merge_group type": (
                put("ci.yml", "on", "merge_group", {"types": ["destroyed"]}),
                "filters merge groups"),
            "closed PRs only": (put("ci.yml", "on", "pull_request", {"types": ["closed"]}),
                                "does not run on pull_request"),
            "PR paths": (put("source-diagnostics.yml", "on", "pull_request", "paths",
                             ["docs/**"]), "filters PRs"),
            "lost PR trigger": (drop("source-diagnostics.yml", "on", "pull_request"),
                                "no pull_request"),
            "PR trigger swapped": (
                put("source-diagnostics.yml", "on", {"pull_request_target": "",
                                                     "merge_group": ""}), "no pull_request"),
            "job-level if": (put("ci.yml", "jobs", "build", "if", "github.event_name == 'push'"),
                             "job-level 'if'"),
            "matrix": (put("source-diagnostics.yml", "jobs", "source-diagnostics", "strategy",
                           {"matrix": {"part": ["1", "2"]}}), "job-level 'strategy'"),
            "renamed check": (put("ci.yml", "jobs", "preflight", "name", "integrity"),
                              "'repository integrity' is reported by []"),
            "renamed job id": (rename_job("ci.yml", "build", "lean-build"),
                               "'build' is reported by []"),
            "duplicate name": (put("lint.yml", "jobs", "lint", "name", "build"),
                               "'build' is reported by"),
            "duplicate job id": (rename_job("lint.yml", "lint", "source-diagnostics"),
                                 "'source-diagnostics' is reported by"),
            "reusable workflow": (put("ci.yml", "jobs", "build", "uses",
                                      "./.github/workflows/lean-build.yml"), "job-level 'uses'"),
            "prerequisite not required": (
                put("ci.yml", "jobs", "build", "needs", ["preflight", "lint"]), "needs 'lint'"),
            "plain workflow group": (put("ci.yml", "concurrency", "group", "ci"),
                                     "is not one of the forms"),
            "ref type, not ref": (
                put("ci.yml", "concurrency", "group",
                    "${{ github.workflow }}-${{ github.ref_type }}"), "is not one of the forms"),
            "short-circuit on a value that is never empty": (
                put("ci.yml", "concurrency", "group",
                    "${{ github.workflow }}-${{ github.ref || github.event.pull_request.number }}"),
                "is not one of the forms"),
            "group shared with another workflow": (
                put("source-diagnostics.yml", "concurrency", "CI-${{ github.ref }}"),
                "is not one of the forms"),
            "pull_request_target form under pull_request": (
                put("source-diagnostics.yml", "concurrency",
                    "${{ github.workflow }}-${{ github.event.merge_group.head_ref || "
                    "github.event.pull_request.number }}"), "is not one of the forms"),
            "workflow names differing only in case": (put("lint.yml", "name", "ci"),
                                                      "share the name 'ci'"),
            "renamed onto another workflow's literal group": (put("ci.yml", "name", "lint"),
                                                               "could match"),
            "another workflow's group starting with an expression": (
                put("lint.yml", "concurrency", "${{ github.head_ref }}"), "could match"),
            "expression job name that can render as a required one": (
                put("lint.yml", "jobs", "lint", "name", "${{ matrix.part }}"),
                "'build' is reported by"),
            "expression in the required job's own name": (
                put("ci.yml", "jobs", "build", "name",
                    "build${{ github.event_name == 'merge_group' && ' (queue)' || '' }}"),
                "expression in its job name"),
            "reusable workflow keyed on the caller's name": (
                put("report.yml", {"name": "Report summary", "on": {"workflow_call": ""},
                                   "concurrency": {"group": "${{ github.workflow }}-"
                                                            "${{ github.ref }}"},
                                   "jobs": {"summary": {}}}), "could match"),
            "job-level group": (put("ci.yml", "jobs", "build", "concurrency",
                                    "${{ github.workflow }}-${{ github.ref }}"),
                                "job-level concurrency group"),
            "push on every branch": (put("ci.yml", "on", "push", ""),
                                     "branches other than main"),
            "push on queue branches": (
                put("source-diagnostics.yml", "on", "push", "branches",
                    ["main", "gh-readonly-queue/main/**"]), "branches other than main"),
            "push on every branch but the queue's": (
                put("ci.yml", "on", "push", {"branches-ignore": ["gh-readonly-queue/**"]}),
                "branches other than main"),
            "push on release branches too": (
                put("ci.yml", "on", "push", {"branches": ["main", "release/*"]}),
                "branches other than main"),
            "this test dropped from Source diagnostics": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"uses": "actions/checkout"}]), "has no step that is exactly"),
            "this test made conditional": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"if": "github.event_name == 'push'", "run": COMMAND}]),
                "has no step that is exactly"),
            "only some of this test": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": COMMAND + " -k equivalent_spellings"}]),
                "has no step that is exactly"),
            "failure of this test ignored": (
                put("ci.yml", "jobs", "preflight", "steps", [{"run": COMMAND + " || true"}]),
                "has no step that is exactly"),
            "this test inside a shell condition": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": 'if [ "$GITHUB_EVENT_NAME" = pull_request ]; then\n'
                             + COMMAND + "\nfi\n"}]), "has no step that is exactly"),
            "this test split over two lines": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"run": COMMAND.replace(" -s", "\n-s")}]), "has no step that is exactly"),
            "this test commented out": (
                put("ci.yml", "jobs", "preflight", "steps", [{"run": "# " + COMMAND}]),
                "has no step that is exactly"),
            "this test with continue-on-error": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"continue-on-error": "true", "run": COMMAND}]),
                "has no step that is exactly"),
            "pull_request_target added to CI": (
                put("ci.yml", "on", "pull_request_target", ""), "also runs on"),
            "pull_request_review added": (
                put("source-diagnostics.yml", "on", "pull_request_review", ""), "also runs on"),
        }
        for label, (change, message) in cases.items():
            with self.subTest(label):
                found = self.check(change)
                self.assertTrue(any(message in problem for problem in found), found)
        self.assertTrue(self.check(documented=list(REQUIRED)[:-1]))


if __name__ == "__main__":
    unittest.main()
