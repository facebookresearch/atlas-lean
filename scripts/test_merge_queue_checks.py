#!/usr/bin/env python3
"""The checks `main` requires must keep reporting on PRs and on merge groups.

A PR can be queued only once the required checks pass on it, and the merge
queue then waits for the same checks on each merge group it builds. This test
fails if a required workflow:

- loses its trigger for PRs (opened, updated, reopened) or for merge groups,
  or filters some of them out;
- can skip the job that reports the check (a skipped job counts as passing):
  a job-level `if`, a matrix, or a prerequisite that is not required itself;
  or can hold it back: a deployment `environment`, whose reviewers or wait
  timers could keep it from running, or a `needs` cycle;
- can skip the job's own check: the job needs a step that is exactly the
  workspace check below followed by the command running it, with no
  step-level `if` or `continue-on-error`, and the job must not have a
  job-level `continue-on-error`;
- leaves Ubuntu runners (the build needs a full Ubuntu VM), runs in a
  container, or runs its steps in a shell other than bash by default or outside
  the repository root, whether the job's `defaults.run` replaces the
  workflow's or is merged with it key by key, or takes `defaults` from an
  expression, which could set any shell or directory;
- sets an environment variable other than `PYTHONDONTWRITEBYTECODE` for the
  whole workflow, for the job or on its checked steps, or has a step that can
  set variables for the steps after it (one that mentions `$GITHUB_ENV`, the
  `github.env` context, the runner's command files or `exportVariable`): a
  variable such as `BASH_ENV` makes bash run a file before each step's
  command, which could exit early and report success. Likewise, no step may
  change `PATH` for later steps (`$GITHUB_PATH`, `github.path`, `addPath`),
  which could put another `git` or `bash` first, except the build's exact
  line adding elan's `bin` directory;
- checks out another ref or repository, or only part of the tree (any checkout
  input beyond credentials, history and progress settings), in that job, so
  that the check would report on the PR or merge group without testing all of
  its tree;
- renames the check, puts an expression in the job's name, lets another job
  report (or possibly report, through an expression in its name) the same
  name, or moves the job into a reusable workflow (which reports
  `caller / callee` instead);
- uses a concurrency group other than the forms below, which are known to
  differ between any two PRs and any two merge groups, or one that another
  workflow's group could match: GitHub concurrency groups are repository-wide
  and case-insensitive, so one run could cancel or replace another's. In a
  reusable workflow, `github.workflow` is the caller's name, and a workflow
  without `name` is known by its path, `.github/workflows/<file>`;
- runs on pushes to any ref but the `main` branch. A push to a PR's branch, or
  of a tag on a PR's head commit, would report the same checks on that commit
  for another tree, and a push to one of the queue's `gh-readonly-queue/...`
  branches, which GitHub creates for each merge group, would report them on
  the merge group's commit and could share its concurrency group.

It also fails if any job of any workflow can write checks or commit statuses:
a check run or status that a job creates with its token is reported by the same
GitHub Actions app as the required checks, so it could stand in for one. Every
job must therefore have explicit token permissions, at the workflow or job
level (a job without them gets the repository's default, which may include
`checks: write`), and none may grant `checks: write`, `statuses: write` or
`write-all`.

It also fails if a required workflow gains another event that could report the
same checks on a PR's head (such as `pull_request_target`), or unless both
`repository integrity` and `source-diagnostics` have a step that is exactly the
workspace check followed by the command that runs this whole test, with no
condition, so that a change that makes one workflow skip its jobs is still
caught by the other. `workflow_dispatch` and `schedule` stay allowed: GitHub
does not count checks from runs those events trigger toward a branch ruleset's
required checks, even on a PR's head commit (GitHub Docs, "Troubleshooting
required status checks", "Checks from some workflow jobs are not evaluated").

Each of those steps starts with the same workspace check (`VERIFY`): `HEAD`
must be `GITHUB_SHA`, the commit the run tests (for a PR, GitHub's test merge
of it into the base branch; for a merge group, the group's commit),
`git status` must succeed and show no changed or added file (ignored build
outputs are allowed), no index entry may be marked skip-worktree or
assume-unchanged (which hide edits from `git status`), and the checkout must
not be sparse. An earlier step that checked out or edited another tree would
otherwise make the check test that tree. The check is in the workflow, not in a
script, because a script in the workspace would be replaced with the tree.

This test reads the workflow files. It cannot see what a step's commands or an
action do when they run (a step could replace bash itself), so it catches
mistakes in workflow edits, not a deliberately malicious one: review of
changes to `.github/` and to the entry points must.

The required checks are the ones listed under "How PRs merge" in
CONTRIBUTING.md. Locally:

    python3 -m pip install -r scripts/requirements-inventory.txt
    python3 -m unittest discover -s scripts -p test_merge_queue_checks.py
"""

from __future__ import annotations

import copy
import os
import re
import subprocess
import tempfile
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
# The workspace check each protected step runs first, with whitespace collapsed.
VERIFY = ('{ changes="$(git status --porcelain --untracked-files=all)" '
          "&& ! git ls-files -v | grep -qv '^H ' "
          '&& [[ "$(git rev-parse HEAD)" == "$GITHUB_SHA" && -z "$changes" '
          '&& "$(git config --type=bool --default=false core.sparseCheckout)" == false ]]; } '
          '|| { echo "::error::The workspace is not $GITHUB_SHA"; exit 1; };')


def exact(command: str) -> str:
    """The one line a protected step must run: the workspace check, then the
    command."""
    return f"{VERIFY} {command}"


STEP_KEYS = {"name", "id", "env", "run", "timeout-minutes", "shell"}
# The only environment variable a required workflow, job or checked step may set.
ENV_ALLOWED = {"PYTHONDONTWRITEBYTECODE"}
# Ways a step can set variables for the steps after it.
# Ways a step can change PATH for the steps after it, and the one such line
# allowed, in `build` only.
SETS_LATER_PATH = re.compile(
    r"GITHUB_PATH|github\s*(?:\.\s*path\b|\[\s*['\"]path['\"]\s*\])|addPath", re.I)
ALLOWED_PATH_LINES = {'echo "$HOME/.elan/bin" >> "$GITHUB_PATH"'}
SETS_LATER_ENV = re.compile(
    r"GITHUB_ENV|github\s*(?:\.\s*env\b|\[\s*['\"]env['\"]\s*\])|_runner_file_commands"
    r"|exportVariable", re.I)
# Runners with the root access and job length the Lean build needs (it adds
# swap); the lighter jobs may use any GitHub-hosted Ubuntu label below.
FULL_UBUNTU = {"ubuntu-26.04", "ubuntu-24.04", "ubuntu-22.04", "ubuntu-latest"}
# Every GitHub-hosted Ubuntu label; `build` needs one of the full x64 VMs above.
UBUNTU = FULL_UBUNTU | {"ubuntu-slim", "ubuntu-26.04-arm", "ubuntu-24.04-arm",
                        "ubuntu-22.04-arm"}
# Checkout inputs that leave the checked-out tree whole and unchanged.
CHECKOUT_INPUTS = {"persist-credentials", "fetch-depth", "fetch-tags", "show-progress", "clean"}
# The command that runs each required job's own check.
ENTRY_POINTS = {
    "repository integrity": "scripts/check.sh preflight",
    "build": "scripts/check.sh build",
    "source-diagnostics": "scripts/run_source_diagnostics.sh",
}

# The protected steps' exact lines, for the fixtures below.
TEST = exact(COMMAND)
PREFLIGHT = exact(ENTRY_POINTS["repository integrity"])
BUILD = exact(ENTRY_POINTS["build"])
DIAGNOSTICS = exact(ENTRY_POINTS["source-diagnostics"])
# Events a required workflow may run on besides its PR event. Pushes must be
# limited to `main`; a workflow_dispatch run reports on a PR's head only if a
# maintainer starts it on that branch.
# Events a required workflow may also run on. Checks from workflow_dispatch and
# schedule runs never satisfy a branch ruleset's required checks (GitHub Docs,
# "Troubleshooting required status checks"), so they cannot stand in for a PR's
# or merge group's run.
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


def pushes_to_other_refs(push) -> bool:
    """Whether a push trigger can run for any ref but the `main` branch: another
    branch, or a tag, which can point at a PR's head commit."""
    push = push if isinstance(push, dict) else {}
    return (set(as_list(push.get("branches"))) != {"main"}
            or bool({"branches-ignore", "tags", "tags-ignore"} & set(push)))


def may_be_named(name: str, check: str) -> bool:
    """Whether a job name, possibly with expressions, can render as `check`."""
    if "${{" not in name:
        return name == check
    prefix, suffix = name.split("${{", 1)[0], name.rsplit("}}", 1)[-1]
    return (check.startswith(prefix) and check.endswith(suffix)
            and len(check) >= len(prefix) + len(suffix))


def check_writers(name: str, workflow: dict) -> list[str]:
    """The jobs in a workflow whose token can create check runs or commit
    statuses, or may: a job's `permissions` replace the workflow's, and a job
    with neither gets the repository's default."""
    found = []
    for job_id, job in (workflow.get("jobs") or {}).items():
        job = job if isinstance(job, dict) else {}
        permissions = job.get("permissions", workflow.get("permissions"))
        if permissions is None:
            found.append(f"{name} job {job_id!r} has no token permissions, so it gets the "
                         "repository's default, which may let it write checks")
        elif permissions not in ("", "read-all") and not (
                isinstance(permissions, dict)
                and all(permissions.get(scope, "none") in ("read", "none")
                        for scope in ("checks", "statuses"))):
            found.append(f"{name} job {job_id!r} can write checks or commit statuses, so it "
                         "could report a required check without running it")
    return found


def needs_itself(workflow: dict, job_id: str) -> bool:
    """Whether a job depends on itself, directly or through other jobs."""
    jobs = workflow.get("jobs") or {}
    seen, pending = set(), as_list((jobs.get(job_id) or {}).get("needs"))
    while pending:
        current = pending.pop()
        if current == job_id:
            return True
        if current not in seen:
            seen.add(current)
            pending += as_list((jobs.get(current) or {}).get("needs"))
    return False


def workflow_name(filename: str, workflow: dict) -> str:
    """`github.workflow` for a workflow file: its `name`, or its path in the
    repository when it has none."""
    return str(workflow.get("name") or f".github/workflows/{filename}")


def shell_code(line: str) -> str:
    """A shell line without its comment, which starts at a `#` that begins a
    word outside quotes."""
    quote, escaped = None, False
    for i, char in enumerate(line):
        if escaped:
            escaped = False
        elif char == "\\" and quote != "'":
            escaped = True
        elif quote:
            quote = None if char == quote else quote
        elif char in "'\"":
            quote = char
        elif char == "#" and (i == 0 or line[i - 1].isspace()):
            return line[:i]
    return line


def step_texts(step) -> tuple[list[str], list[str]]:
    """A step's command lines, without shell comments, and its `env` and `with`
    values, as text."""
    if not isinstance(step, dict):
        return [], []
    lines = [shell_code(line).strip() for line in str(step.get("run", "")).splitlines()]
    values = []
    for key in ("env", "with"):
        value = step.get(key) or {}
        values += [str(v) for v in value.values()] if isinstance(value, dict) else [str(value)]
    return lines, values


def sets_later_env(step) -> bool:
    """Whether a step can set variables for the steps after it."""
    lines, values = step_texts(step)
    return any(SETS_LATER_ENV.search(text) for text in lines + values)


def changes_later_path(step, allowed: set[str]) -> bool:
    """Whether a step can change PATH for the steps after it, other than with an
    allowed line."""
    lines, values = step_texts(step)
    return (any(SETS_LATER_PATH.search(value) for value in values)
            or any(SETS_LATER_PATH.search(line) and line not in allowed for line in lines))


def default_runs(job: dict, workflow: dict) -> list[dict]:
    """The `defaults.run` settings a job's steps may inherit. GitHub's runner
    replaces the workflow's block with the job's as a whole, but GitHub's
    documentation can be read as merging them key by key, so return both."""
    def block(level):
        defaults = level.get("defaults")
        run = defaults.get("run") if isinstance(defaults, dict) else None
        return run if isinstance(run, dict) else None

    job_run, workflow_run = block(job), block(workflow)
    replaced = job_run if job_run is not None else workflow_run or {}
    return [replaced, {**(workflow_run or {}), **(job_run or {})}]


def default_shells(job: dict, workflow: dict) -> list[str]:
    """The shells a step without `shell` may run in: the inherited default, or
    bash, or sh for a job that runs in a container."""
    return sorted({run.get("shell") or ("sh" if job.get("container") else "bash")
                   for run in default_runs(job, workflow)})


def runs_exactly(step, command: str, shell: str = "bash") -> bool:
    """Whether a step runs exactly the workspace check and then this command,
    as one line, unconditionally, in bash, with nothing able to ignore its
    failure. `shell` is the inherited default."""
    if not isinstance(step, dict):
        return False
    run = str(step.get("run", "")).strip()
    # Spelling out the defaults (the repository root, failures not ignored) is fine.
    return (set(step) <= STEP_KEYS | {"working-directory", "continue-on-error"}
            and step.get("working-directory", ".") in (".", "./")
            and is_false(step.get("continue-on-error", "false"))
            and not env_problems(step) and step.get("shell", shell) == "bash"
            and "\n" not in run and " ".join(run.split()) == exact(command))


def is_false(value) -> bool:
    """Whether a YAML value is the literal boolean false."""
    return isinstance(value, str) and value in ("false", "False", "FALSE")


def env_problems(level: dict) -> list[str]:
    """The environment variables a workflow, job or step sets beyond those
    allowed; an `env` given as an expression could set any of them."""
    env = level.get("env")
    if env in (None, ""):
        return []
    if not isinstance(env, dict):
        return ["(an expression)"]
    return sorted(set(env) - ENV_ALLOWED)


def problems(workflows: dict[str, dict], documented: list[str]) -> list[str]:
    """Every way the required checks could stop reporting; empty when none."""
    found = []
    if documented != list(REQUIRED):
        found.append(f"CONTRIBUTING lists {documented}, not {list(REQUIRED)}")
    for name, workflow in workflows.items():
        found += check_writers(name, workflow)
    names: dict[str, list[str]] = {}
    for name, workflow in workflows.items():
        names.setdefault(workflow_name(name, workflow).casefold(), []).append(name)
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
               else workflow_name(name, workflow), scope, concurrency_group(setting))
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
        if "push" in triggers and pushes_to_other_refs(triggers["push"]):
            found.append(f"{name} runs on pushes to refs other than the main branch")
        extra = sorted(set(triggers) - OTHER_EVENTS - {pr_event})
        if extra:
            found.append(f"{name} also runs on {extra}, which could report its checks "
                         "for another tree")
        (_, job_id), = reporters[check]
        job = workflow["jobs"][job_id]
        if "${{" in job.get("name", ""):
            found.append(f"{check!r} has an expression in its job name, so it may report "
                         "another name on some events")
        for key in ("if", "strategy", "uses", "environment"):
            if key in job:
                found.append(f"{check!r} has a job-level {key!r}")
        steps = as_list(job.get("steps"))
        shells = default_shells(job, workflow)
        # One label, written alone, as a one-item list, or under `labels` alone.
        labels = job.get("runs-on")
        if isinstance(labels, dict) and set(labels) == {"labels"}:
            labels = labels["labels"]
        runner = labels[0] if isinstance(labels, list) and len(labels) == 1 else labels
        if not isinstance(runner, str) or runner not in (
                FULL_UBUNTU if check == "build" else UBUNTU):
            found.append(f"{check!r} runs on {job.get('runs-on')!r}, not an Ubuntu runner "
                         "it can run on")
        for shell in shells:
            if shell != "bash":
                found.append(f"{check!r} runs its steps in {shell!r} by default, not bash")
        if any(run.get("working-directory", ".") not in (".", "./")
               for run in default_runs(job, workflow)):
            found.append(f"{check!r} runs its steps outside the repository root by default")
        if not all(any(runs_exactly(step, ENTRY_POINTS[check], shell) for step in steps)
                   for shell in shells):
            found.append(f"{check!r} has no step that is exactly the workspace check followed "
                         f"by {ENTRY_POINTS[check]!r}")
        for step in as_list(job.get("steps")):
            # GitHub resolves action names case-insensitively and ignores empty
            # path components, so compare the repository the action comes from.
            path = str(step.get("uses", "")).split("@", 1)[0] if isinstance(step, dict) else ""
            if [part.casefold() for part in path.split("/") if part][:2] == ["actions", "checkout"]:
                extra = sorted(set(step.get("with") or {}) - CHECKOUT_INPUTS)
                if extra:
                    found.append(f"{check!r} checks out with {extra}, which can change the tree")
        if job.get("container"):
            found.append(f"{check!r} runs in a container")
        if not is_false(job.get("continue-on-error", "false")):
            found.append(f"{check!r} has a job-level continue-on-error, which can report a "
                         "failed job as successful")
        for scope, level in (("workflow", workflow), ("job", job)):
            if env_problems(level):
                found.append(f"{check!r} gets {env_problems(level)} from its {scope} env, "
                             "which could change how its steps run")
        if any(sets_later_env(step) for step in steps):
            found.append(f"{check!r} has a step that can set variables for the steps after it")
        allowed = ALLOWED_PATH_LINES if check == "build" else set()
        if any(changes_later_path(step, allowed) for step in steps):
            found.append(f"{check!r} has a step that can change PATH for the steps after it")
        for scope, level in (("workflow", workflow), ("job", job)):
            defaults = level.get("defaults")
            if defaults not in (None, "") and not (
                    isinstance(defaults, dict) and isinstance(defaults.get("run", {}), dict)):
                found.append(f"{check!r} gets defaults from an expression in its {scope}, "
                             "which could set any shell or directory")
        for prerequisite in as_list(job.get("needs")):
            if (name, prerequisite) not in required_jobs:
                found.append(f"{check!r} needs {prerequisite!r}, which is not required")
        if needs_itself(workflow, job_id):
            found.append(f"{check!r} needs itself through `needs`, so it never runs")
        # A new run in a concurrency group cancels the group's pending run even
        # without cancel-in-progress.
        group = concurrency_group(workflow.get("concurrency"))
        if group:
            if normalised(group) not in SAFE_GROUPS[pr_event]:
                found.append(f"{name} concurrency group {group!r} is not one of the forms "
                             f"known to differ per {pr_event} and per merge group")
            start = literal_start(workflow_name(name, workflow), group)
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
        if check in RUN_THIS_TEST and not all(any(runs_exactly(step, COMMAND, shell)
                                                  for step in steps) for shell in shells):
            found.append(f"{check!r} has no step that is exactly the workspace check followed "
                         f"by {COMMAND!r}")
    return found


# A minimal configuration that passes, for the checker's own tests below; the
# live workflows are checked separately.
FIXTURE = {
    "ci.yml": {
        "name": "CI",
        "permissions": {"contents": "read"},
        "on": {"push": {"branches": ["main"]},
               "pull_request": {"types": ["opened", "synchronize", "reopened"]},
               "merge_group": {"types": ["checks_requested"]}},
        "concurrency": {"group": "${{ github.workflow }}-${{ github.ref }}"},
        "jobs": {"preflight": {"name": "repository integrity", "runs-on": "ubuntu-24.04",
                               "steps": [{"run": PREFLIGHT},
                                         {"run": "pip install"}, {"run": TEST}]},
                 "build": {"needs": "preflight", "runs-on": "ubuntu-24.04", "steps": [
                     {"uses": "actions/checkout@v7", "with": {"persist-credentials": "false"}},
                     {"name": "Build", "run": BUILD},
                     {"if": "github.ref == 'refs/heads/main'", "uses": "actions/cache/save@v5"}]}},
    },
    "source-diagnostics.yml": {
        "name": "Source diagnostics",
        "permissions": {"contents": "read"},
        "on": {"push": {"branches": "main"}, "pull_request": "", "merge_group": ""},
        "jobs": {"source-diagnostics": {"runs-on": "ubuntu-24.04", "steps": [
            {"uses": "actions/checkout"},
            {"name": "Test", "run": TEST.replace(" -s", "  -s") + "\n"},
            {"id": "diagnostics", "shell": "bash", "run": DIAGNOSTICS}]}},
    },
    "bump-guard.yml": {
        "name": "Bump guard",
        "on": {"pull_request_target": "", "merge_group": ""},
        "jobs": {"guard": {"permissions": {"contents": "read", "pull-requests": "read"}}},
    },
    "lint.yml": {"on": {"pull_request": {"paths": ["docs/**"]}}, "permissions": "read-all",
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
                       lambda workflows: (
                           put("ci.yml", "defaults", {"run": {"shell": "sh"}})(workflows),
                           put("ci.yml", "jobs", "preflight", "defaults",
                               {"run": {"shell": "bash"}})(workflows),
                           put("ci.yml", "jobs", "build", "defaults",
                               {"run": {"shell": "bash"}})(workflows)),
                       put("source-diagnostics.yml", "jobs", "source-diagnostics",
                           {"runs-on": "ubuntu-24.04", "env": {"PYTHONDONTWRITEBYTECODE": "1"},
                            "steps": [{"env": {"PYTHONDONTWRITEBYTECODE": "1"}, "run": TEST},
                                      {"id": "diagnostics",
                                       "run": DIAGNOSTICS}]}),
                       put("ci.yml", "jobs", "build", "runs-on", ["ubuntu-26.04"]),
                       put("ci.yml", "jobs", "build", "steps",
                           [{"run": '# Use $GITHUB_PATH rather than $GITHUB_ENV for elan.\n'
                                    'elan-init -y  # The next line adds elan to $GITHUB_PATH.\n'
                                    'echo "$HOME/.elan/bin" >> "$GITHUB_PATH"  # for lake'},
                            {"run": BUILD}]),
                       put("ci.yml", "jobs", "build", "runs-on", {"labels": ["ubuntu-24.04"]}),
                       lambda workflows: (
                           put("ci.yml", "jobs", "build", "continue-on-error", "false")(workflows),
                           put("ci.yml", "jobs", "build", "steps",
                               [{"working-directory": "./", "continue-on-error": "false",
                                 "run": BUILD}])(workflows)),
                       put("source-diagnostics.yml", "jobs", "source-diagnostics", "runs-on",
                           "ubuntu-26.04-arm"),
                       put("report.yml", {"on": {"pull_request": ""}, "concurrency": {
                           "group": "${{ github.workflow }}-${{ github.ref }}"},
                           "jobs": {"report": {"permissions": {}}}}),
                       put("nightly.yml", {"name": "CI-nightly", "on": {"schedule": ""},
                                           "permissions": {"contents": "read",
                                                           "checks": "read"},
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
                                     "refs other than the main branch"),
            "push on queue branches": (
                put("source-diagnostics.yml", "on", "push", "branches",
                    ["main", "gh-readonly-queue/main/**"]), "refs other than the main branch"),
            "push on every branch but the queue's": (
                put("ci.yml", "on", "push", {"branches-ignore": ["gh-readonly-queue/**"]}),
                "refs other than the main branch"),
            "push on release branches too": (
                put("ci.yml", "on", "push", {"branches": ["main", "release/*"]}),
                "refs other than the main branch"),
            "this test dropped from Source diagnostics": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"uses": "actions/checkout"}]), "has no step that is exactly"),
            "this test made conditional": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"if": "github.event_name == 'push'", "run": TEST}]),
                "has no step that is exactly"),
            "only some of this test": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": TEST + " -k equivalent_spellings"}]),
                "has no step that is exactly"),
            "failure of this test ignored": (
                put("ci.yml", "jobs", "preflight", "steps", [{"run": TEST + " || true"}]),
                "has no step that is exactly"),
            "this test inside a shell condition": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": 'if [ "$GITHUB_EVENT_NAME" = pull_request ]; then\n'
                             + COMMAND + "\nfi\n"}]), "has no step that is exactly"),
            "this test split over two lines": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"run": TEST.replace(" -s", "\n-s")}]), "has no step that is exactly"),
            "build step made conditional": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"if": "github.event_name != 'merge_group'",
                      "run": BUILD}]),
                "followed by 'scripts/check.sh build'"),
            "build step allowed to fail": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"continue-on-error": "true", "run": BUILD}]),
                "followed by 'scripts/check.sh build'"),
            "diagnostics step made conditional, with a decoy that names the scanners": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": TEST},
                     {"run": "python3 -m py_compile scripts/check_duplicate_defs.py "
                             "scripts/check_hypothesis_debt.py scripts/run_source_diagnostics.sh"},
                     {"if": "github.event_name == 'pull_request'",
                      "run": DIAGNOSTICS}]),
                "followed by 'scripts/run_source_diagnostics.sh'"),
            "diagnostics step with another shell": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": TEST},
                     {"shell": "bash {0} || true", "run": DIAGNOSTICS}]),
                "followed by 'scripts/run_source_diagnostics.sh'"),
            "build job defaulting to sh": (
                put("ci.yml", "jobs", "build", "defaults", {"run": {"shell": "sh"}}),
                "followed by 'scripts/check.sh build'"),
            "Source diagnostics in a container": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "container",
                    "python:3.12-bookworm"),
                "'source-diagnostics' has no step that is exactly"),
            "container with bash only on the checked steps": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics",
                    {"container": "python:3.12-bookworm", "runs-on": "ubuntu-24.04",
                     "steps": [{"shell": "bash", "run": TEST},
                               {"shell": "bash", "run": DIAGNOSTICS}]}),
                "by default, not bash"),
            "job defaults replacing a workflow bash default in a container": (
                lambda workflows: (
                    put("ci.yml", "defaults", {"run": {"shell": "bash"}})(workflows),
                    put("ci.yml", "jobs", "preflight", "container", "python:3.12-bookworm")(
                        workflows),
                    put("ci.yml", "jobs", "preflight", "defaults",
                        {"run": {"working-directory": "."}})(workflows)),
                "by default, not bash"),
            "build sparse checkout": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"uses": "actions/checkout@v7",
                      "with": {"sparse-checkout": "MathlibExt/\n!DomainsTest/Biology/"}},
                     {"run": BUILD}]), "which can change the tree"),
            "build sparse checkout with a mixed-case action name": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"uses": "Actions/Checkout@v7",
                      "with": {"sparse-checkout": "MathlibExt/"}},
                     {"run": BUILD}]), "which can change the tree"),
            "build sparse checkout with a trailing slash in the action name": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"uses": "actions/checkout/@v7",
                      "with": {"sparse-checkout": "MathlibExt/"}},
                     {"run": BUILD}]), "which can change the tree"),
            "build running in scripts/ by default": (
                put("ci.yml", "jobs", "build", "defaults",
                    {"run": {"working-directory": "scripts"}}),
                "outside the repository root"),
            "a step that adds to $GITHUB_PATH": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": 'echo "$PWD/bin" >> "$GITHUB_PATH"'}, {"run": BUILD}]),
                "change PATH for the steps after it"),
            "a step that writes the github.path context": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": "echo /tmp/bin >> '${{ github.path }}'"}, {"run": BUILD}]),
                "change PATH for the steps after it"),
            "addPath in an action's script": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"uses": "actions/github-script@v7",
                      "with": {"script": "core.addPath('/tmp/bin')"}},
                     {"run": TEST}, {"run": DIAGNOSTICS}]),
                "change PATH for the steps after it"),
            "the allowed elan line followed by another PATH change": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": 'echo "$HOME/.elan/bin" >> "$GITHUB_PATH"\n'
                             'echo "$PWD/bin" >> "$GITHUB_PATH"'}, {"run": BUILD}]),
                "change PATH for the steps after it"),
            "a job's run defaults from an expression": (
                put("ci.yml", "jobs", "build", "defaults",
                    {"run": "${{ fromJSON(vars.CI_RUN_DEFAULTS) }}"}),
                "gets defaults from an expression in its job"),
            "a workflow's defaults from an expression": (
                put("ci.yml", "defaults", "${{ fromJSON(vars.CI_DEFAULTS) }}"),
                "gets defaults from an expression in its workflow"),
            "a workflow whose token can write checks": (
                put("report.yml", {"on": {"pull_request": ""}, "permissions": {"checks": "write"},
                                   "jobs": {"report": {}}}), "can write checks"),
            "a workflow whose token can write commit statuses": (
                put("report.yml", {"on": {"pull_request": ""},
                                   "permissions": {"statuses": "write"},
                                   "jobs": {"report": {}}}), "commit statuses"),
            "a GITHUB_ENV write before a comment": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": 'echo "BASH_ENV=x" >> "$GITHUB_ENV" # for later steps'},
                     {"run": BUILD}]), "set variables for the steps after it"),
            "a quoted # before a GITHUB_PATH write": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": 'echo "/tmp/#bin" >> "$GITHUB_PATH"'}, {"run": BUILD}]),
                "change PATH for the steps after it"),
            "a job with write-all permissions": (
                put("ci.yml", "jobs", "build", "permissions", "write-all"), "can write checks"),
            "checks permission from an expression": (
                put("ci.yml", "jobs", "build", "permissions",
                    {"checks": "${{ vars.CHECKS }}"}), "can write checks"),
            "a job without token permissions": (
                put("report.yml", {"on": {"pull_request": ""}, "jobs": {"report": {}}}),
                "gets the repository's default"),
            "the elan PATH line in Source diagnostics": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": 'echo "$HOME/.elan/bin" >> "$GITHUB_PATH"'},
                     {"run": TEST}, {"run": DIAGNOSTICS}]),
                "change PATH for the steps after it"),
            "build on a runner group": (
                put("ci.yml", "jobs", "build", "runs-on",
                    {"group": "large", "labels": "ubuntu-24.04"}), "not an Ubuntu runner"),
            "build step in another directory": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"working-directory": "scripts", "run": BUILD}]),
                "followed by 'scripts/check.sh build'"),
            "job-level continue-on-error from an expression": (
                put("ci.yml", "jobs", "build", "continue-on-error", "${{ false }}"),
                "job-level continue-on-error"),
            "build behind a deployment environment": (
                put("ci.yml", "jobs", "build", "environment", "production"),
                "has a job-level 'environment'"),
            "build needing itself": (put("ci.yml", "jobs", "build", "needs", ["build"]),
                                     "'build' needs itself"),
            "preflight and build needing each other": (
                put("ci.yml", "jobs", "preflight", "needs", "build"),
                "'repository integrity' needs itself"),
            "Source diagnostics on an unknown Ubuntu label": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "runs-on",
                    "ubuntu-typo"), "not an Ubuntu runner"),
            "an unnamed workflow known by the path CI is named after": (
                lambda workflows: (
                    put("ci.yml", "name", ".github/workflows/report.yml")(workflows),
                    put("report.yml", {"on": {"pull_request": ""}, "concurrency": {
                        "group": "${{ github.workflow }}-${{ github.ref }}"},
                        "jobs": {"report": {}}})(workflows)),
                "share the name"),
            "push of tags only": (put("ci.yml", "on", "push", {"tags": ["v*"]}),
                                  "pushes to refs other than the main branch"),
            "push of main and tags": (
                put("ci.yml", "on", "push", {"branches": ["main"], "tags": ["v*"]}),
                "pushes to refs other than the main branch"),
            "workflow shell kept under a job's working-directory default": (
                lambda workflows: (
                    put("ci.yml", "defaults", {"run": {"shell": "bash {0} || true"}})(
                        workflows),
                    put("ci.yml", "jobs", "build", "defaults",
                        {"run": {"working-directory": "."}})(workflows)),
                "'build' runs its steps in 'bash {0} || true' by default"),
            "workflow working directory kept under a job's shell default": (
                lambda workflows: (
                    put("ci.yml", "defaults", {"run": {"working-directory": "scripts"}})(
                        workflows),
                    put("ci.yml", "jobs", "build", "defaults",
                        {"run": {"shell": "bash"}})(workflows)),
                "'build' runs its steps outside the repository root"),
            "build without the workspace check": (
                put("ci.yml", "jobs", "build", "steps", [{"run": "scripts/check.sh build"}]),
                "followed by 'scripts/check.sh build'"),
            "workspace check without the HEAD comparison": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": BUILD.replace(
                        '"$(git rev-parse HEAD)" == "$GITHUB_SHA" && ', "")}]),
                "followed by 'scripts/check.sh build'"),
            "this test without the workspace check": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": COMMAND}, {"run": DIAGNOSTICS}]),
                "followed by " + repr(COMMAND)),
            "job-level continue-on-error": (
                put("ci.yml", "jobs", "build", "continue-on-error", "true"),
                "job-level continue-on-error"),
            "BASH_ENV for the whole workflow": (
                put("ci.yml", "env", {"BASH_ENV": "scripts/exit0.sh"}),
                "from its workflow env"),
            "BASH_ENV for the job": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "env",
                    {"BASH_ENV": "scripts/exit0.sh"}), "from its job env"),
            "BASH_ENV on the checked step": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"run": TEST},
                     {"id": "diagnostics", "env": {"BASH_ENV": "scripts/exit0.sh"},
                      "run": DIAGNOSTICS}]),
                "followed by 'scripts/run_source_diagnostics.sh'"),
            "job env from an expression": (
                put("ci.yml", "jobs", "build", "env", "${{ fromJSON(vars.BUILD_ENV) }}"),
                "from its job env"),
            "a step that writes $GITHUB_ENV": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": 'echo "BASH_ENV=$PWD/scripts/exit0.sh" >> "$GITHUB_ENV"'},
                     {"run": BUILD}]), "set variables for the steps after it"),
            "a step that writes the github.env context": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"run": "echo 'BASH_ENV=scripts/exit0.sh' >> '${{ github.env }}'"},
                     {"run": BUILD}]), "set variables for the steps after it"),
            "github['env'] through a step env alias": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"env": {"FILE": "${{ github['env'] }}"},
                      "run": 'echo BASH_ENV=scripts/exit0.sh >> "$FILE"'},
                     {"run": BUILD}]), "set variables for the steps after it"),
            "exportVariable in an action's script": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "steps",
                    [{"uses": "actions/github-script@v7",
                      "with": {"script": "core.exportVariable('BASH_ENV', 'scripts/exit0.sh')"}},
                     {"run": TEST}, {"run": DIAGNOSTICS}]),
                "set variables for the steps after it"),
            "required job in a container with a bash default": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics",
                    {"container": "python:3.12-bookworm", "runs-on": "ubuntu-24.04",
                     "defaults": {"run": {"shell": "bash"}},
                     "steps": FIXTURE["source-diagnostics.yml"]["jobs"]
                                     ["source-diagnostics"]["steps"]}),
                "runs in a container"),
            "build in a container": (
                put("ci.yml", "jobs", "build", "container", "ubuntu:24.04"),
                "runs in a container"),
            "build on ubuntu-slim": (put("ci.yml", "jobs", "build", "runs-on", "ubuntu-slim"),
                                     "not an Ubuntu runner it can run on"),
            "Source diagnostics on Windows": (
                put("source-diagnostics.yml", "jobs", "source-diagnostics", "runs-on",
                    "windows-latest"), "not an Ubuntu runner"),
            "CI defaulting to sh": (
                put("ci.yml", "defaults", {"run": {"shell": "sh"}}),
                "followed by 'scripts/check.sh preflight'"),
            "preflight dropped": (
                put("ci.yml", "jobs", "preflight", "steps", [{"run": TEST}]),
                "followed by 'scripts/check.sh preflight'"),
            "build checks out the PR's head branch": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"uses": "actions/checkout@v7", "with": {"ref": "${{ github.head_ref || "
                                                                     "'main' }}"}}]),
                "which can change the tree"),
            "build checks out another repository": (
                put("ci.yml", "jobs", "build", "steps",
                    [{"uses": "actions/checkout@v7", "with": {"repository": "someone/fork"}}]),
                "which can change the tree"),
            "this test commented out": (
                put("ci.yml", "jobs", "preflight", "steps", [{"run": "# " + COMMAND}]),
                "has no step that is exactly"),
            "this test with continue-on-error": (
                put("ci.yml", "jobs", "preflight", "steps",
                    [{"continue-on-error": "true", "run": TEST}]),
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


class WorkspaceCheck(unittest.TestCase):
    """VERIFY, run as GitHub runs a step without `shell` (`bash -e`), in a scratch
    repository, before a command that prints RAN."""

    def run_check(self, change=None, sha=None):
        with tempfile.TemporaryDirectory() as scratch:
            repo, home = Path(scratch, "repo"), Path(scratch, "home")
            repo.mkdir()
            home.mkdir()
            directory = str(repo)
            # Isolate every git command from the contributor's configuration, with
            # a home outside the repository: some git builds write files there.
            environment = {"PATH": os.environ["PATH"], "HOME": str(home),
                           "XDG_CONFIG_HOME": str(home), "GIT_CONFIG_NOSYSTEM": "1",
                           "GIT_CONFIG_GLOBAL": os.devnull}

            def git(*args):
                return subprocess.run(["git", "-C", directory, *args], check=True,
                                      capture_output=True, text=True,
                                      env=environment).stdout.strip()

            git("init", "-q")
            (repo / ".gitignore").write_text(".lake/\n")
            (repo / "file").write_text("one\n")
            git("add", ".")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "one")
            (repo / "file").write_text("two\n")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qam", "two")
            head = git("rev-parse", "HEAD")
            if change:
                change(repo, git)
            result = subprocess.run(["bash", "-e", "-c", exact("echo RAN")], cwd=directory,
                                    env={**environment, "GITHUB_SHA": sha or head},
                                    capture_output=True, text=True)
            try:
                return result.returncode, result.stdout
            finally:
                (repo / ".git" / "index").chmod(0o644)

    def test_runs_the_command_on_the_tested_commit(self):
        def ignored_build_output(repo, git):
            (repo / ".lake").mkdir()
            (repo / ".lake" / "out").write_text("")

        self.assertEqual(self.run_check(), (0, "RAN\n"))
        self.assertEqual(self.run_check(ignored_build_output), (0, "RAN\n"))

    def test_refuses_any_other_workspace(self):
        def unreadable_index(repo, git):
            (repo / ".git" / "index").chmod(0)

        changes = {
            "another commit reported": lambda: self.run_check(sha="0" * 40),
            "another commit checked out": lambda: self.run_check(
                lambda repo, git: git("checkout", "-q", "HEAD~1")),
            "files from another commit": lambda: self.run_check(
                lambda repo, git: git("checkout", "-q", "HEAD~1", "--", ".")),
            "an edited file": lambda: self.run_check(
                lambda repo, git: (repo / "file").write_text("edited\n")),
            "an added file": lambda: self.run_check(
                lambda repo, git: (repo / "added.py").write_text("")),
            "a sparse checkout": lambda: self.run_check(
                lambda repo, git: git("config", "core.sparseCheckout", "true")),
            "an edit hidden by skip-worktree": lambda: self.run_check(
                lambda repo, git: (git("update-index", "--skip-worktree", "file"),
                                   (repo / "file").write_text("edited\n"))),
            "an edit hidden by assume-unchanged": lambda: self.run_check(
                lambda repo, git: (git("update-index", "--assume-unchanged", "file"),
                                   (repo / "file").write_text("edited\n"))),
        }
        if os.geteuid() != 0:  # root can read an unreadable index
            changes["git status failing"] = lambda: self.run_check(unreadable_index)
        for label, run in changes.items():
            with self.subTest(label):
                code, output = run()
                self.assertNotEqual(code, 0)
                self.assertNotIn("RAN", output)


if __name__ == "__main__":
    unittest.main()
