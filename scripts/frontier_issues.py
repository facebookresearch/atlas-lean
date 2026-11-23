#!/usr/bin/env python3
"""Keep one GitHub issue open for every task on the ATLAS graph's frontier.

    python scripts/frontier_issues.py frontier blueprint --output build/frontier.json
    python scripts/frontier_issues.py sync build/frontier.json --repo OWNER/NAME [--apply]

`frontier` runs in the wiki build, after `sync_wiki.py lean-facts` has added
the Lean's facts, and needs Autoform. It writes the tasks that can start now:

- `formalize`: a field of the taxonomy with at least one article whose
  statement can be written in Lean, or whose statement is in Lean and whose
  proof can start, by Autoform's own readiness rule (the derived `can_state`
  and `can_prove` states behind `autoform work list`). The field's issue
  lists them all, grouped by Lean module;
- `dag-work`: a planned article with Autoform's `not_ready` flag and no
  unresolved statement or proof prerequisites (graph rule 12).

`sync` needs only the standard library and a token in GITHUB_TOKEN. It opens
an issue for each task without one, updates an issue whose task changed, and
closes an open issue whose task left the frontier: as completed when its node
is finished, as not planned otherwise, and reopens it when the task is back.
It never reopens an issue a person closed as not planned, and it keeps the
labels people added while it owns the kind and `area:` labels. Without --apply it only reports the plan. Writes are
paced and capped per run (--max-writes), so a large backlog opens over several
runs within GitHub's limits on content creation.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path

SCHEMA = "atlas-frontier/v2"
KINDS = {"formalize": "task:formalize", "dag-work": "task:dag-work"}
GRAPH_LABEL = "math graph"
TASK_MARK = re.compile(r"<!-- atlas-task: (\S+) -->")
NODE_MARK = re.compile(r"<!-- atlas-node: (\S+) -->")
BODY_END = "<!-- atlas-generated-end -->"
# Added when the sync closes an unfinished task that left the frontier, so it can reopen the issue when the task
# is ready again; an issue a person closed as not planned has no such line and stays closed.
OFF_FRONTIER = "<!-- atlas-closed: off-frontier -->"
STATEMENT_LIMIT = 1500
DEPENDENCY_LIMIT = 20
# Results listed in one field issue; the rest are on the field's page. Keeps a body far below GitHub's limit.
ITEM_LIMIT = 100
TITLE_LIMIT = 200
LABEL_COLORS = {"task:formalize": "0064e0", "task:dag-work": "f7b928"}
AREA_COLOR = "c5def5"
SKILL = ".agents/skills/atlas-solve-issue/SKILL.md"


# ---------------------------------------------------------------------------
# frontier: the tasks that can start now, from the built graph


def task_key(node_id: str, declarations: list[str]) -> str:
    """A formalization task is keyed by its Lean declaration, which survives moves of its page and the removal of
    article ids (deprecated in Autoform 0.8, removed in 0.9); a node without Lean is keyed by its path."""
    return f"decl:{declarations[0]}" if declarations else f"node:{node_id}"


def statement_of(page: Path) -> str:
    """The page's statement: its text after the title, up to the first section."""
    try:
        text = page.read_text(encoding="utf-8")
    except OSError:
        return ""
    text = re.sub(r"\A---\n.*?\n---\n", "", text, flags=re.S)
    text = re.sub(r"\A\s*# [^\n]*\n", "", text)
    text = re.split(r"(?m)^## ", text, maxsplit=1)[0].strip()
    if len(text) > STATEMENT_LIMIT:
        text = text[:STATEMENT_LIMIT].rsplit(" ", 1)[0] + " …"
    return text


def module_folders(blueprint: Path) -> set[Path]:
    """The folders whose page is a Lean module's page (`navigation: module` in its annotation): generate_wiki
    lays out one per module, and splits a long one into transparent parts below it."""
    folders = set()
    for source in sorted((blueprint / "links").rglob("*.jsonl")):
        for line in source.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            annotation = json.loads(line)
            ours = annotation.get("extensions", {}).get("org.autoform", {})
            if isinstance(ours, dict) and ours.get("navigation") == "module":
                for subject in annotation.get("subject", []):
                    page = (source.parent / subject["uri"]).resolve()
                    if page.name == "README.md":
                        folders.add(page.parent)
    return folders


def taxonomy_fields(path: Path) -> dict[str, set[str]]:
    """Read field boundaries; a bad taxonomy must not look like a new frontier."""
    try:
        subjects = json.loads(path.read_text(encoding="utf-8"))["subjects"]
        result = {name: {entry["slug"] for entry in subject["fields"]} for name, subject in subjects.items()}
        if not result or any(not isinstance(slug, str) or not slug for fields in result.values() for slug in fields):
            raise ValueError("invalid subject or field slugs")
        return result
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        raise ValueError(f"cannot read frontier taxonomy: {error}") from error


def page_title(page: Path) -> str | None:
    try:
        for line in page.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    except OSError:
        pass
    return None


def build_frontier(blueprint: Path, commit: str | None = None, repo: str | None = None) -> dict:
    from autoform_cli.runtime import load_runtime_graph  # the wiki build installs the pinned Autoform

    blueprint = blueprint.resolve()
    repository = blueprint.parent
    runtime = load_runtime_graph(blueprint)
    nodes = {node.id: node for node in runtime.nodes}
    resolved_leaves = sum(bool(node.lean_targets and node.dispatchable) for node in runtime.nodes)
    if not resolved_leaves:
        raise ValueError("no resolved Lean leaves: build the vault with lean-facts before computing the frontier")

    def page(node) -> Path:
        path = Path(node.article_path)
        return path if path.is_absolute() else (repository / path)

    def relative(node) -> str:
        return page(node).resolve().relative_to(repository).as_posix()

    dependents: dict[str, int] = {}
    for node in runtime.nodes:
        if not node.status.proved:
            for dependency in node.dependencies:
                dependents[dependency] = dependents.get(dependency, 0) + 1

    tasks, finished = [], []
    missing_ids = 0
    dag_nodes: list[str] = []
    for node in runtime.nodes:
        declarations = [target.declaration for target in node.lean_targets]
        key = task_key(node.id, declarations)
        if node.status.proved or node.mathlib:
            # Both keys: a proved result often has a new name, so its issue is found by its page too.
            finished += [key, f"node:{node.id}"]
            continue
        if node.dispatchable and not node.article_id:
            missing_ids += 1
        if (node.assertions.not_ready and not node.formalizable and not declarations
                and not node.catalog and page(node).name != "README.md"):
            dag_nodes.append(node.id)
            if node.status.waiting_on:
                continue
            kind, phase = "dag-work", None
        elif (
            node.dispatchable
            and not node.assertions.not_ready
            and declarations
            and not node.status.waiting_on
        ):
            kind, phase = "formalize", "proof" if node.status.stated else "statement"
        else:
            continue
        path = relative(node)
        parts = Path(path).parts
        tasks.append({
            "key": key,
            "kind": kind,
            "phase": phase,
            "node_id": node.id,
            "article_id": node.article_id,
            "title": node.title,
            "page": path,
            "subject": parts[2] if len(parts) > 3 else None,
            "statement": statement_of(page(node)),
            "declarations": declarations,
            "dependencies": [
                {"title": nodes[dependency].title, "page": relative(nodes[dependency])}
                for dependency in node.dependencies
                if dependency in nodes
            ],
            "unlocks": dependents.get(node.id, 0),
        })
    tasks.sort(key=lambda task: (-task["unlocks"], task["page"]))
    # Two pages for one declaration (`autoform audit`'s duplicate-lean-target) are one task, under the first page.
    seen: set[str] = set()
    tasks = [task for task in tasks if not (task["key"] in seen or seen.add(task["key"]))]

    # One formalization issue per field of the taxonomy (subject, then field): a node of the graph's hierarchy
    # with its own page, a few hundred in all, where a Lean module would give over a thousand. The issue lists
    # the field's ready results grouped by Lean module, the usual unit of one PR. Nodes to expand stay one issue
    # each.
    modules = module_folders(blueprint)
    roadmap = (blueprint / "roadmap").resolve()
    fields = taxonomy_fields(repository / "scripts" / "taxonomy.json")

    def module_of(path: Path) -> Path:
        for folder in path.parents:
            if folder in modules:
                return folder
            if folder == roadmap:
                break
        return path.parent

    def field_of(path: Path) -> Path:
        parts = path.relative_to(roadmap).parts
        if len(parts) < 2:
            return roadmap
        subject = roadmap / parts[0]
        if len(parts) >= 3 and parts[1] in fields.get(parts[0], ()):
            return subject / parts[1]
        return subject

    def node_name(folder: Path) -> str:
        return folder.relative_to(roadmap).as_posix() if folder != roadmap else "."

    groups: dict[Path, list[dict]] = {}
    module_titles: dict[Path, str] = {}
    for task in tasks:
        if task["kind"] == "formalize":
            path = (repository / task["page"]).resolve()
            folder = module_of(path)
            readme = folder / "README.md"
            if folder not in module_titles:
                module_titles[folder] = page_title(readme) or folder.name
            task["module"] = module_titles[folder]
            task["module_page"] = readme.relative_to(repository).as_posix() if readme.is_file() else task["page"]
            groups.setdefault(field_of(path), []).append(task)
    unfinished = {
        field_of(page(node).resolve())
        for node in runtime.nodes
        if node.dispatchable and not node.status.proved and not node.mathlib
    }
    for node in runtime.nodes:
        folder = field_of(page(node).resolve())
        if (node.status.proved or node.mathlib) and folder not in unfinished:
            finished.append(f"field:{node_name(folder)}")

    grouped = [task for task in tasks if task["kind"] == "dag-work"]
    for folder, items in groups.items():
        readme = folder / "README.md"
        parts = Path(items[0]["page"]).parts
        # Modules that unblock the most come first, and within a module its results that unblock the most.
        weight: dict[str, int] = {}
        for item in items:
            weight[item["module_page"]] = weight.get(item["module_page"], 0) + item["unlocks"]
        items.sort(key=lambda item: (-weight[item["module_page"]], item["module_page"], -item["unlocks"], item["page"]))
        grouped.append({
            "key": f"field:{node_name(folder)}",
            "kind": "formalize",
            "phase": "field",
            "node_id": node_name(folder),
            "article_id": None,
            "title": page_title(readme) or folder.name,
            "page": readme.relative_to(repository).as_posix() if readme.is_file() else items[0]["page"],
            "subject": parts[2] if len(parts) > 3 else None,
            "statement": "",
            "declarations": [],
            "dependencies": [],
            "items": [
                {key: item[key] for key in ("title", "page", "phase", "declarations", "unlocks", "module", "module_page")}
                for item in items
            ],
            "unlocks": sum(item["unlocks"] for item in items),
        })
    grouped.sort(key=lambda task: (-task["unlocks"], task["kind"] != "dag-work", task["page"]))
    return {
        "schema": SCHEMA,
        "commit": commit,
        "repo": repo,
        "source_revision": runtime.source_revision,
        "resolved_leaves": resolved_leaves,
        "missing_ids": missing_ids,
        "dag_nodes": sorted(dag_nodes),
        "tasks": grouped,
        "finished": sorted(set(finished)),
    }


# ---------------------------------------------------------------------------
# sync: make the issues match the frontier


def issue_title(task: dict) -> str:
    verb = {"field": "Formalize", "proof": "Prove", "statement": "State in Lean"}.get(task["phase"] or "", "Expand")
    title = f"{verb}: {task['title']}"
    return title if len(title) <= TITLE_LIMIT else title[: TITLE_LIMIT - 1].rstrip() + "…"


def issue_labels(task: dict) -> list[str]:
    labels = [KINDS[task["kind"]], GRAPH_LABEL]
    if task.get("subject"):
        labels.append(f"area:{task['subject']}")
    return labels


def managed(label: str) -> bool:
    """A label the sync owns on a task issue: the task kind and the area. Others are left as people set them."""
    return label in KINDS.values() or label.startswith("area:")


def merged_labels(issue: dict, task: dict) -> list[str]:
    kept = {label["name"] for label in issue.get("labels", []) if not managed(label["name"])}
    return sorted(kept | set(issue_labels(task)))


def issue_body(task: dict, repo: str) -> str:
    blob = f"https://github.com/{repo}/blob/main/"
    kind = {
        "field": "formalize the ready results of this field, grouped by Lean module",
        "proof": "prove a result whose statement is already in Lean",
        "statement": "write this article's statement in Lean",
        None: "break this node down into child articles (DAG work)",
    }[task["phase"]]
    lines = [
        f"<!-- atlas-task: {task['key']} -->",
        f"<!-- atlas-node: {task['node_id']} -->",
        f"**Task:** {kind}.",
        "",
    ]
    if task["statement"]:
        lines += ["> " + line if line else ">" for line in task["statement"].splitlines()]
        lines.append("")
    items = task.get("items") or []
    if items:
        modules = len({item.get("module_page") for item in items})
        lines += [f"Ready now: {len(items)} result(s) in {modules} module(s), with prerequisites satisfied for the listed phase.", ""]
        current = None
        for item in items[:ITEM_LIMIT]:
            if item.get("module_page") != current:
                current = item.get("module_page")
                if lines[-1] != "":
                    lines.append("")
                lines += [f"**[{item.get('module', current)}]({blob}{urllib.parse.quote(current or '')})**", ""]
            verb = "Prove" if item["phase"] == "proof" else "State"
            lean = ", ".join(f"`{name}`" for name in item["declarations"])
            lines.append(f"- [ ] {verb} [{item['title']}]({blob}{urllib.parse.quote(item['page'])})" + (f" ({lean})" if lean else ""))
        if len(items) > ITEM_LIMIT:
            rest = items[ITEM_LIMIT:]
            lines += ["", f"… and {len(rest)} more in {len({item.get('module_page') for item in rest})} module(s). See the `blueprint-frontier` artifact from the Blueprint Pages run for the complete list."]
        lines.append("")
    lines.append(f"- **Page:** [`{task['page']}`]({blob}{urllib.parse.quote(task['page'])})")
    if task["declarations"]:
        lines.append("- **Lean:** " + ", ".join(f"`{name}`" for name in task["declarations"]))
    dependencies = task["dependencies"]
    if dependencies:
        shown = ", ".join(
            f"[{dependency['title']}]({blob}{urllib.parse.quote(dependency['page'])})"
            for dependency in dependencies[:DEPENDENCY_LIMIT]
        )
        more = len(dependencies) - DEPENDENCY_LIMIT
        lines.append(f"- **Depends on:** {shown}" + (f", and {more} more" if more > 0 else ""))
    if task["unlocks"]:
        what = "these results" if task["phase"] == "field" else "this one"
        lines.append(f"- **Unblocks:** {task['unlocks']} unfinished node(s) that depend on {what}")
    lines += ["", "### Done when", ""]
    if task["phase"] == "field":
        lines += [
            "- each result above is stated or proved in its library with no `sorry`, axioms or `native_decide`, and",
            "  its `theorem_wanted` or `def_wanted` is gone (`WantedExt/README.md`);",
            "- each article's annotation names the declaration that now formalizes it, and `scripts/check.sh` passes.",
            "",
            "Work it one module at a time: a PR usually takes one module of the list, or part of one. The list follows",
            "the graph on `main`: a result leaves it once finished, newly unblocked ones join it, and the issue",
            "closes when nothing in the field is ready.",
        ]
    elif task["kind"] == "dag-work":
        lines += [
            "- replace the node and its annotation, repoint incoming links, and preserve the prerequisites",
            "  each replacement still needs. Keep blocked leaves planned (graph rules 10–13);",
            "- the wiki build passes and the PR meets the review requirements in rule 16.",
        ]
    elif task["phase"] == "proof":
        lines += [
            "- the result is proved in its library with no `sorry`, axioms or `native_decide`, and the",
            "  `theorem_wanted` is gone (`WantedExt/README.md`);",
            "- the article's annotation names the proved declaration, and `scripts/check.sh` passes.",
        ]
    else:
        lines += [
            "- the statement or definition is in Lean, matching the page clause by clause, with tests in the",
            "  matching `*Test` library;",
            "- the article's annotation names the declaration, and `scripts/check.sh` passes.",
        ]
    lines += [
        "",
        f"How to work it: [atlas-solve-issue]({blob}{SKILL}). Coordinate before starting. Use a non-closing",
        "reference (`Part of #…`) for a field issue; report completion in the PR and let sync close the issue.",
        "",
        "<sub>Opened from the graph on `main` by `scripts/frontier_issues.py`. It is updated while the",
        "task is on the frontier and closed when its field or node is finished or leaves it.</sub>",
        BODY_END,
    ]
    # Strip reserved markers from graph-derived prose before adding machine-readable headers.
    rendered = "\n".join(lines[2:-1]).replace("<!-- atlas-", "&lt;!-- atlas-")
    # Only modules visible in this issue can be reserved through the issue.
    modules = sorted({item["module_page"] for item in items[:ITEM_LIMIT]
                      if re.fullmatch(r"blueprint/roadmap/[^\s<>]+\.md", item["module_page"])})
    headers = lines[:2] + [f"<!-- atlas-module: {module} -->" for module in modules]
    return "\n".join([*headers, rendered, BODY_END]) + "\n"


class RateLimited(Exception):
    pass


class GitHub:
    """The few REST calls `sync` makes, with pacing between writes."""

    def __init__(self, repo: str, token: str, api: str = "https://api.github.com", pause: float = 1.0) -> None:
        self.repo, self.token, self.api, self.pause = repo, token, api.rstrip("/"), pause

    def request(self, method: str, path: str, payload: dict | None = None, attempts: int = 3):
        url = path if path.startswith("http") else f"{self.api}{path}"
        data = json.dumps(payload).encode() if payload is not None else None
        for attempt in range(attempts):
            request = urllib.request.Request(url, data=data, method=method, headers={
                "Accept": "application/vnd.github+json",
                "Authorization": f"Bearer {self.token}",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "atlas-frontier-issues",
            })
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
                    body = response.read()
                    if method != "GET" and self.pause:
                        time.sleep(self.pause)
                    return json.loads(body) if body else None, response.headers
            except urllib.error.HTTPError as error:
                limited = error.code == 429 or (
                    error.code == 403 and (
                        error.headers.get("retry-after") or error.headers.get("x-ratelimit-remaining") == "0"
                        or b"rate limit" in error.read().lower()
                    )
                )
                if not limited:
                    raise
                if attempt + 1 == attempts:
                    raise RateLimited(f"{method} {path}: GitHub rate limit") from error
                wait = int(error.headers.get("retry-after") or 60)
                time.sleep(min(max(wait, 1), 120))
        raise RateLimited(f"{method} {path}: GitHub rate limit")

    def paginate(self, path: str) -> list:
        items, url = [], f"{self.api}{path}"
        while url:
            page, headers = self.request("GET", url)
            items.extend(page)
            match = re.search(r'<([^>]+)>;\s*rel="next"', headers.get("link", "") or "")
            url = match.group(1) if match else None
        return items

    def labels(self) -> set[str]:
        return {label["name"] for label in self.paginate(f"/repos/{self.repo}/labels?per_page=100")}

    def create_label(self, name: str, color: str) -> None:
        self.request("POST", f"/repos/{self.repo}/labels", {"name": name, "color": color})

    def issues(self, label: str) -> list[dict]:
        query = urllib.parse.urlencode({"labels": label, "state": "all", "per_page": 100})
        return [issue for issue in self.paginate(f"/repos/{self.repo}/issues?{query}") if "pull_request" not in issue]

    def create_issue(self, title: str, body: str, labels: list[str]) -> dict:
        return self.request("POST", f"/repos/{self.repo}/issues", {"title": title, "body": body, "labels": labels})[0]

    def read_issue(self, number: int) -> dict:
        return self.request("GET", f"/repos/{self.repo}/issues/{number}")[0]

    def update_issue(self, number: int, **fields) -> dict:
        return self.request("PATCH", f"/repos/{self.repo}/issues/{number}", fields)[0]


@dataclass
class Plan:
    labels: list[str] = field(default_factory=list)
    create: list[dict] = field(default_factory=list)
    update: list[tuple[dict, dict]] = field(default_factory=list)
    reopen: list[tuple[dict, dict]] = field(default_factory=list)
    close: list[tuple[dict, str]] = field(default_factory=list)
    unchanged: int = 0
    declined: int = 0

    def writes(self) -> int:
        return len(self.labels) + len(self.create) + len(self.update) + len(self.reopen) + len(self.close)


def marks(issue: dict) -> tuple[str | None, str | None]:
    # Only headers count; issue prose can contain example markers.
    lines = (issue.get("body") or "").splitlines()[:2]
    task = TASK_MARK.fullmatch(lines[0]) if lines else None
    node = NODE_MARK.fullmatch(lines[1]) if len(lines) > 1 else None
    return (task.group(1), node.group(1)) if task and node else (None, None)


def notes(issue: dict) -> str:
    """Human text after the generated section; don't replace it on refresh."""
    return (issue.get("body") or "").partition(BODY_END)[2].replace(OFF_FRONTIER, "")


def task_body(task: dict, repo: str, issue: dict) -> str:
    existing_notes = notes(issue)
    return issue_body(task, repo).rstrip("\n") + existing_notes if existing_notes.strip() else issue_body(task, repo)


def plan_sync(frontier: dict, issues: list[dict], existing_labels: set[str], repo: str) -> Plan:
    if frontier.get("schema") != SCHEMA:
        raise ValueError(f"expected a {SCHEMA} frontier, got {frontier.get('schema')!r}")
    if (frontier.get("repo") != repo or not frontier.get("source_revision")
            or not isinstance(frontier.get("commit"), str) or not re.fullmatch(r"[0-9a-f]{40}", frontier["commit"])
            or type(frontier.get("resolved_leaves")) is not int or frontier["resolved_leaves"] <= 0
            or type(frontier.get("missing_ids")) is not int or frontier["missing_ids"] < 0
            or any(not isinstance(frontier.get(key), list) for key in ("tasks", "finished", "dag_nodes"))):
        raise ValueError("incomplete or mismatched frontier snapshot; rerun the validated wiki build")
    plan = Plan()
    tasks = frontier["tasks"]
    wanted_labels = sorted({label for task in tasks for label in issue_labels(task)} | set(KINDS.values()))
    plan.labels = [label for label in wanted_labels if label not in existing_labels]

    by_key: dict[str, dict] = {}
    by_node: dict[str, dict] = {}
    # The newest issue wins when two carry the same mark.
    for issue in sorted(issues, key=lambda issue: issue["number"]):
        key, node = marks(issue)
        if key:
            by_key[key] = issue
        if key and node:
            by_node[node] = issue

    # Match one-to-one: first by task key, then by node path for a task whose key changed (its declaration was
    # renamed, or it gained one). An issue another task already holds by key is never taken by path, so a page
    # that takes over an old path does not take over the moved task's issue.
    if len({task["key"] for task in tasks}) != len(tasks):
        raise ValueError("frontier has duplicate task keys")
    matched: set[int] = set()
    pairs: dict[str, dict] = {}
    for task in tasks:
        issue = by_key.get(task["key"])
        if issue is not None and issue["number"] not in matched:
            pairs[task["key"]] = issue
            matched.add(issue["number"])
    for task in tasks:
        if task["key"] in pairs:
            continue
        issue = by_node.get(task["node_id"])
        if issue is None or issue["number"] in matched:
            continue
        pairs[task["key"]] = issue
        matched.add(issue["number"])

    for task in tasks:
        issue = pairs.get(task["key"])
        if issue is None:
            plan.create.append(task)
            continue
        if issue["state"] == "closed":
            suspended = OFF_FRONTIER in (issue.get("body") or "")
            if issue.get("state_reason") == "not_planned" and not suspended:
                plan.declined += 1
            else:
                plan.reopen.append((issue, task))
            continue
        have = {label["name"] for label in issue.get("labels", [])}
        title, body = issue_title(task), task_body(task, repo, issue)
        if issue["title"] != title or (issue.get("body") or "") != body or have != set(merged_labels(issue, task)):
            plan.update.append((issue, task))
        else:
            plan.unchanged += 1

    finished = set(frontier.get("finished", []))
    for issue in issues:
        key, node = marks(issue)
        if issue["state"] != "open" or issue["number"] in matched or not (key and node):
            continue
        done = key in finished or f"node:{node}" in finished
        if key.startswith("node:") and KINDS["dag-work"] in {label.get("name") for label in issue.get("labels", [])}:
            done = done or node not in frontier["dag_nodes"]
        plan.close.append((issue, "completed" if done else "not_planned"))
    return plan


def apply_plan(plan: Plan, github: GitHub, repo: str, max_writes: int, log=print) -> int:
    """Carry out the plan, closes first, then updates, then creates, up to max_writes. Returns the writes made."""
    done = 0

    def room() -> bool:
        return done < max_writes

    try:
        for label in plan.labels:
            if not room():
                return done
            github.create_label(label, LABEL_COLORS.get(label, AREA_COLOR))
            done += 1
        for issue, reason in plan.close:
            if not room():
                return done
            live = github.read_issue(issue["number"])
            if live["state"] != "open" or marks(live) != marks(issue):
                continue
            issue = live
            fields = {"state": "closed", "state_reason": reason}
            if reason == "not_planned":
                fields["body"] = (issue.get("body") or "").rstrip("\n") + "\n\n" + OFF_FRONTIER + "\n"
            github.update_issue(issue["number"], **fields)
            done += 1
        for reopen, updates in ((True, plan.reopen), (False, plan.update)):
            for issue, task in updates:
                if not room():
                    return done
                live = github.read_issue(issue["number"])
                if marks(live) != marks(issue):
                    continue
                if reopen and (live["state"] != "closed" or live.get("state_reason") != issue.get("state_reason")
                               or live.get("updated_at") != issue.get("updated_at")):
                    continue
                if not reopen and live["state"] != "open":
                    continue
                fields = {"state": "open"} if reopen else {}
                github.update_issue(issue["number"], title=issue_title(task),
                                    body=task_body(task, repo, live), labels=merged_labels(live, task), **fields)
                done += 1
        for task in plan.create:
            if not room():
                return done
            github.create_issue(issue_title(task), issue_body(task, repo), issue_labels(task))
            done += 1
    except RateLimited as error:
        log(f"stopped after {done} write(s): {error}; the next run continues")
    return done


def summarize(plan: Plan, frontier: dict, applied: int | None, max_writes: int) -> str:
    counts: dict[str, int] = {}
    for task in frontier["tasks"]:
        counts[task["kind"]] = counts.get(task["kind"], 0) + 1
    mode = "dry run: nothing was written" if applied is None else f"applied {applied} write(s), at most {max_writes} per run"
    lines = [
        "## Frontier issues",
        "",
        f"Graph at `{(frontier.get('commit') or 'unknown')[:12]}`: "
        + ", ".join(f"{count} {kind}" for kind, count in sorted(counts.items())) + f" task(s). {mode}.",
        "",
        "| Action | Count |",
        "| --- | ---: |",
        f"| create labels | {len(plan.labels)} |",
        f"| open issues | {len(plan.create)} |",
        f"| update issues | {len(plan.update)} |",
        f"| reopen issues | {len(plan.reopen)} |",
        f"| close issues | {len(plan.close)} |",
        f"| unchanged | {plan.unchanged} |",
        f"| closed as not planned, left closed | {plan.declined} |",
    ]
    if frontier.get("missing_ids"):
        lines += ["", f"Issue publication is blocked: {frontier['missing_ids']} unfinished leaves lack IDs (#5524)."]
    if plan.create:
        lines += ["", "First issues to open:", ""]
        lines += [f"- {issue_title(task)} (`{task['page']}`)" for task in plan.create[:20]]
    if plan.close:
        lines += ["", "Issues to close:", ""]
        lines += [f"- #{issue['number']} {issue['title']} ({reason})" for issue, reason in plan.close[:20]]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    frontier = commands.add_parser("frontier", help="write the frontier of the built graph")
    frontier.add_argument("blueprint", type=Path)
    frontier.add_argument("--output", type=Path, required=True)
    frontier.add_argument("--commit", default=os.environ.get("GITHUB_SHA"))
    frontier.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"))
    sync = commands.add_parser("sync", help="make the task issues match a frontier")
    sync.add_argument("frontier", type=Path)
    sync.add_argument("--repo", required=True)
    sync.add_argument("--expected-commit", help="bind sync to the build commit")
    sync.add_argument("--apply", action="store_true", help="write to GitHub; without it, only report the plan")
    sync.add_argument("--max-writes", type=int, default=250)
    sync.add_argument("--pause", type=float, default=1.0, help="seconds between writes")
    sync.add_argument("--summary", type=Path, help="append a Markdown summary here (GITHUB_STEP_SUMMARY)")
    args = parser.parse_args(argv)

    if args.command == "frontier":
        result = build_frontier(args.blueprint, args.commit, args.repo)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
        kinds = {}
        for task in result["tasks"]:
            kinds[task["kind"]] = kinds.get(task["kind"], 0) + 1
        print(f"{len(result['tasks'])} task(s) {kinds}, {len(result['finished'])} finished node(s) -> {args.output}")
        return 0

    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("GITHUB_TOKEN is not set", file=sys.stderr)
        return 2
    frontier_data = json.loads(args.frontier.read_text(encoding="utf-8"))
    if args.apply and not args.expected_commit:
        parser.error("publication requires --expected-commit from the build")
    if args.expected_commit and frontier_data.get("commit") != args.expected_commit:
        parser.error("frontier snapshot is not from the expected commit")
    if args.apply and frontier_data.get("missing_ids") != 0:
        parser.error("issue publication requires every unfinished formalizable leaf to have an article ID (#5524)")
    github = GitHub(args.repo, token, os.environ.get("GITHUB_API_URL", "https://api.github.com"), args.pause)
    issues = {issue["number"]: issue for label in KINDS.values() for issue in github.issues(label)}
    plan = plan_sync(frontier_data, list(issues.values()), github.labels(), args.repo)
    applied = apply_plan(plan, github, args.repo, args.max_writes) if args.apply else None
    summary = summarize(plan, frontier_data, applied, args.max_writes)
    print(summary)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as handle:
            handle.write(summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
