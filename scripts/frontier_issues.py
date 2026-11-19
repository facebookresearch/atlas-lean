#!/usr/bin/env python3
"""Keep one GitHub issue open for every task on the ATLAS graph's frontier.

    python scripts/frontier_issues.py frontier blueprint --output build/frontier.json
    python scripts/frontier_issues.py sync build/frontier.json --repo OWNER/NAME [--apply]
    python scripts/frontier_issues.py claim --event "$GITHUB_EVENT_PATH" --repo OWNER/NAME

`frontier` runs in the wiki build, after `sync_wiki.py lean-facts` has added
the Lean's facts, and needs Autoform. It writes the tasks that can start now:

- `formalize`: a field of the taxonomy with at least one article whose
  statement can be written in Lean, or whose statement is in Lean and whose
  proof can start, by Autoform's own readiness rule (the derived `can_state`
  and `can_prove` states behind `autoform work list`). The field's issue
  lists them all, grouped by Lean module;
- `dag-work`: an article whose annotation carries
  `"org.atlas-wiki": {"unexpanded": true}`, a node still to be broken down
  (rule 12 of the graph rules in docs/BLUEPRINT.md).

`sync` needs only the standard library and a token in GITHUB_TOKEN. It opens
an issue for each task without one, updates an issue whose task changed, and
closes an open issue whose task left the frontier: as completed when its node
is finished, as not planned otherwise, and reopens it when the task is back.
It never reopens an issue a person closed as not planned, and it keeps the
labels people added while it owns the kind and `area:` labels. Without --apply it only reports the plan. Writes are
paced and capped per run (--max-writes), so a large backlog opens over several
runs within GitHub's limits on content creation.

`claim` answers a `/claim` or `/unclaim` comment on a task issue: `/claim`
assigns the commenter when nobody holds the task, and `/unclaim` releases it.
A maintainer may `/unclaim @someone` to free a task held by someone else.
`sync` releases a claim held for more than seven days with no open pull
request that references the issue, as an AutoformBot claim lapses.
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

SCHEMA = "atlas-frontier/v1"
OWN = "org.atlas-wiki"
UNEXPANDED = "unexpanded"
KINDS = {"formalize": "task:formalize", "dag-work": "task:dag-work"}
GRAPH_LABEL = "math graph"
TASK_MARK = re.compile(r"<!-- atlas-task: (\S+) -->")
NODE_MARK = re.compile(r"<!-- atlas-node: (\S+) -->")
# Added when the sync closes an unfinished task that left the frontier, so it can reopen the issue when the task
# is ready again; an issue a person closed as not planned has no such line and stays closed.
OFF_FRONTIER = "<!-- atlas-closed: off-frontier -->"
# A claim lapses after this many days without an open pull request that references the issue, as an
# AutoformBot claim lapses after seven days.
CLAIM_DAYS = 7
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


def unexpanded_pages(blueprint: Path) -> set[Path]:
    """The pages whose annotation marks them as nodes still to expand."""
    marked = set()
    for source in sorted((blueprint / "links").rglob("*.jsonl")):
        for line in source.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            annotation = json.loads(line)
            own = annotation.get("extensions", {}).get(OWN, {})
            if isinstance(own, dict) and own.get(UNEXPANDED) is True:
                for subject in annotation.get("subject", []):
                    marked.add((source.parent / subject["uri"]).resolve())
    return marked


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


def taxonomy_fields(path: Path) -> dict[str, set[str]] | None:
    """Each subject's field slugs from scripts/taxonomy.json, or None without it."""
    try:
        subjects = json.loads(path.read_text(encoding="utf-8"))["subjects"]
    except (OSError, ValueError, KeyError):
        return None
    return {name: {field["slug"] for field in subject.get("fields", [])} for name, subject in subjects.items()}


def page_title(page: Path) -> str | None:
    try:
        for line in page.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    except OSError:
        pass
    return None


def build_frontier(blueprint: Path, commit: str | None = None) -> dict:
    from autoform_cli.runtime import load_runtime_graph  # the wiki build installs the pinned Autoform

    blueprint = blueprint.resolve()
    repository = blueprint.parent
    runtime = load_runtime_graph(blueprint)
    nodes = {node.id: node for node in runtime.nodes}
    marked = unexpanded_pages(blueprint)

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
    for node in runtime.nodes:
        declarations = [target.declaration for target in node.lean_targets]
        key = task_key(node.id, declarations)
        if node.status.proved or node.mathlib:
            # Both keys: a proved result often has a new name, so its issue is found by its page too.
            finished += [key, f"node:{node.id}"]
            continue
        if page(node).resolve() in marked:
            kind, phase = "dag-work", None
        elif (
            node.dispatchable
            and not node.assertions.not_ready
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
        if len(parts) >= 3 and (fields is None or parts[1] in fields.get(parts[0], ())):
            return subject / parts[1]
        return subject

    def node_name(folder: Path) -> str:
        return folder.relative_to(roadmap).as_posix() if folder != roadmap else "."

    groups: dict[Path, list[dict]] = {}
    for task in tasks:
        if task["kind"] == "formalize":
            path = (repository / task["page"]).resolve()
            folder = module_of(path)
            task["module"] = page_title(folder / "README.md") or folder.name
            task["module_page"] = (folder / "README.md").relative_to(repository).as_posix()
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
        "source_revision": runtime.source_revision,
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
        lines += [f"Ready now: {len(items)} result(s) in {modules} module(s), each with every prerequisite finished.", ""]
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
            lines += ["", f"… and {len(rest)} more in {len({item.get('module_page') for item in rest})} module(s), listed on the field's page."]
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
            "- the node's `unexpanded` marker is gone, and its children are in the graph: `theorem_wanted` or",
            "  `def_wanted` statements in `WantedExt` for leaves, marked nodes for the rest (graph rules 12-13);",
            "- `scripts/check_graph_rules.py` and the `build the wiki` job pass, and a code owner approved the PR.",
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
        f"How to work it: [atlas-solve-issue]({blob}{SKILL}). Comment `/claim` before you start (`/unclaim`",
        "if you stop), and reference this issue in the PR (`Closes #<this issue>` when it finishes the list).",
        "",
        "<sub>Opened from the graph on `main` by `scripts/frontier_issues.py`. It is updated while the",
        "task is on the frontier and closed when its field or node is finished or leaves it.</sub>",
    ]
    return "\n".join(lines) + "\n"


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

    def update_issue(self, number: int, **fields) -> dict:
        return self.request("PATCH", f"/repos/{self.repo}/issues/{number}", fields)[0]

    def timeline(self, number: int) -> list[dict]:
        return self.paginate(f"/repos/{self.repo}/issues/{number}/timeline?per_page=100")

    def unassign(self, number: int, logins: list[str]) -> None:
        self.request("DELETE", f"/repos/{self.repo}/issues/{number}/assignees", {"assignees": logins})

    def comment(self, number: int, body: str) -> None:
        self.request("POST", f"/repos/{self.repo}/issues/{number}/comments", {"body": body})


@dataclass
class Plan:
    labels: list[str] = field(default_factory=list)
    create: list[dict] = field(default_factory=list)
    update: list[tuple[dict, dict]] = field(default_factory=list)
    reopen: list[tuple[dict, dict]] = field(default_factory=list)
    close: list[tuple[dict, str]] = field(default_factory=list)
    release: list[tuple[dict, list[str]]] = field(default_factory=list)
    unchanged: int = 0
    declined: int = 0

    def writes(self) -> int:
        return (len(self.labels) + len(self.create) + len(self.update) + len(self.reopen) + len(self.close)
                + 2 * len(self.release))


def marks(issue: dict) -> tuple[str | None, str | None]:
    body = issue.get("body") or ""
    task, node = TASK_MARK.search(body), NODE_MARK.search(body)
    return (task.group(1) if task else None, node.group(1) if node else None)


def plan_sync(frontier: dict, issues: list[dict], existing_labels: set[str], repo: str) -> Plan:
    if frontier.get("schema") != SCHEMA:
        raise ValueError(f"expected a {SCHEMA} frontier, got {frontier.get('schema')!r}")
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
        if node:
            by_node[node] = issue

    # Match one-to-one: first by task key, then by node path for a task whose key changed (its declaration was
    # renamed, or it gained one). An issue another task already holds by key is never taken by path, so a page
    # that takes over an old path does not take over the moved task's issue.
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
        title, body = issue_title(task), issue_body(task, repo)
        if issue["title"] != title or (issue.get("body") or "") != body or have != set(merged_labels(issue, task)):
            plan.update.append((issue, task))
        else:
            plan.unchanged += 1

    finished = set(frontier.get("finished", []))
    for issue in issues:
        key, node = marks(issue)
        if issue["state"] != "open" or issue["number"] in matched or not (key or node):
            continue
        done = key in finished or f"node:{node}" in finished
        plan.close.append((issue, "completed" if done else "not_planned"))
    return plan


def parse_time(value: str) -> float:
    from datetime import datetime

    return datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()


def stale_claims(issue: dict, timeline: list[dict], now: float, days: int = CLAIM_DAYS) -> list[str]:
    """The assignees of an open task issue whose claim has lapsed: assigned more than `days` ago, with no open
    pull request referencing the issue."""
    holders = [assignee["login"] for assignee in issue.get("assignees", [])]
    if issue.get("state") != "open" or not holders:
        return []
    for event in timeline:
        source = (event.get("source") or {}).get("issue") or {}
        if event.get("event") == "cross-referenced" and source.get("pull_request") and source.get("state") == "open":
            return []
    assigned: dict[str, float] = {}
    for event in timeline:
        if event.get("event") == "assigned" and event.get("assignee") and event.get("created_at"):
            assigned[event["assignee"]["login"]] = parse_time(event["created_at"])
    return [holder for holder in holders if holder in assigned and now - assigned[holder] > days * 86400]


def plan_releases(plan: Plan, issues: list[dict], timeline_of, now: float, limit: int = 100) -> None:
    """Add to the plan the lapsed claims on task issues that stay open; `timeline_of(number)` reads a timeline.

    At most `limit` timelines are read per run, least recently updated first, to keep within the token's
    request budget; the rest wait for the next run.
    """
    closing = {issue["number"] for issue, _ in plan.close}
    held = [
        issue for issue in issues
        if issue["state"] == "open" and issue.get("assignees") and issue["number"] not in closing and marks(issue)[0]
    ]
    held.sort(key=lambda issue: issue.get("updated_at") or "")
    for issue in held[:limit]:
        lapsed = stale_claims(issue, timeline_of(issue["number"]), now)
        if lapsed:
            plan.release.append((issue, lapsed))


def apply_plan(plan: Plan, github: GitHub, repo: str, max_writes: int, log=print) -> int:
    """Carry out the plan: labels, closes, lapsed claims, updates, then creates, up to max_writes. Returns the
    writes made."""
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
            fields = {"state": "closed", "state_reason": reason}
            if reason == "not_planned":
                fields["body"] = (issue.get("body") or "").rstrip("\n") + "\n\n" + OFF_FRONTIER + "\n"
            github.update_issue(issue["number"], **fields)
            done += 1
        for issue, lapsed in plan.release:
            if done + 2 > max_writes:
                return done
            github.unassign(issue["number"], lapsed)
            holders = ", ".join(f"@{login}" for login in lapsed)
            github.comment(issue["number"], (
                f"Released the claim of {holders}: {CLAIM_DAYS} days without an open pull request that references "
                "this issue. Comment `/claim` to take the task again."
            ))
            done += 2
        for issue, task in plan.reopen + plan.update:
            if not room():
                return done
            github.update_issue(issue["number"], state="open", title=issue_title(task),
                                body=issue_body(task, repo), labels=merged_labels(issue, task))
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
        f"| release lapsed claims | {len(plan.release)} |",
        f"| unchanged | {plan.unchanged} |",
        f"| closed as not planned, left closed | {plan.declined} |",
    ]
    if plan.create:
        lines += ["", "First issues to open:", ""]
        lines += [f"- {issue_title(task)} (`{task['page']}`)" for task in plan.create[:20]]
    if plan.close:
        lines += ["", "Issues to close:", ""]
        lines += [f"- #{issue['number']} {issue['title']} ({reason})" for issue, reason in plan.close[:20]]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# claim: /claim and /unclaim on task issues

CLAIM = re.compile(r"\A/(claim|unclaim)(?:[ \t]+@([A-Za-z0-9](?:[A-Za-z0-9-]{0,38})))?[ \t]*\Z")
# Repository roles that may free a task someone else holds (the collaborator permission API's role_name).
MAINTAINER_ROLES = frozenset({"admin", "maintain", "write"})
# GitHub's limit on assignees per issue.
MAX_HOLDERS = 10


@dataclass(frozen=True)
class ClaimDecision:
    """What to do about one comment: assign or unassign someone, and what to say."""

    add: str | None = None
    remove: str | None = None
    reply: str | None = None
    react: bool = False


def claim_command(event: dict) -> tuple[str, str | None] | None:
    """The command a comment gives, as (verb, named login), or None when it is not a claim command."""
    issue, comment = event.get("issue") or {}, event.get("comment") or {}
    if not issue or not comment or issue.get("pull_request") or event.get("action", "created") != "created":
        return None
    if (comment.get("user") or {}).get("type") == "Bot":
        return None
    lines = (comment.get("body") or "").strip().splitlines()
    command = CLAIM.match(lines[0].strip()) if lines else None
    return (command.group(1), command.group(2)) if command else None


def decide_claim(event: dict, maintainer: bool = False) -> ClaimDecision | None:
    """The answer to a comment, or None when the comment is not a claim command on a task issue.

    `event["issue"]` should be the issue as it is now, not as the event captured it, so that two claims
    answered one after the other see each other; `maintainer` says whether the commenter may write to the
    repository.
    """
    issue, comment = event.get("issue") or {}, event.get("comment") or {}
    if not issue or not comment or issue.get("pull_request") or event.get("action", "created") != "created":
        return None
    if not {label.get("name") for label in issue.get("labels", [])} & set(KINDS.values()):
        return None
    user = comment.get("user") or {}
    if user.get("type") == "Bot":
        return None
    lines = (comment.get("body") or "").strip().splitlines()
    command = CLAIM.match(lines[0].strip()) if lines else None
    if not command:
        return None
    verb, named = command.group(1), command.group(2)
    login = user.get("login", "")
    holders = [assignee.get("login") for assignee in issue.get("assignees", [])]

    if verb == "claim":
        if named and named.casefold() != login.casefold():
            return ClaimDecision(reply=f"@{login} `/claim` takes the task for yourself; @{named} can claim it.")
        if issue.get("state") != "open":
            return ClaimDecision(reply=f"@{login} this task is closed, so it can't be claimed.")
        if login in holders:
            return ClaimDecision(react=True)
        # A field issue lists many modules, so several people may hold it at once, one module each, up to
        # GitHub's ten assignees; they say in the comment which module they take.
        shared = "<!-- atlas-task: field:" in (issue.get("body") or "")
        if holders and shared and len(holders) < MAX_HOLDERS:
            return ClaimDecision(add=login, react=True)
        if holders:
            others = ", ".join(f"@{holder}" for holder in holders)
            return ClaimDecision(reply=(
                f"@{login} this task is already claimed by {others}. Ask them first; if it has stalled, a "
                f"maintainer can free it with `/unclaim @{holders[0]}`."
            ))
        return ClaimDecision(add=login, react=True)

    target = named or login
    if target.casefold() != login.casefold() and not maintainer:
        return ClaimDecision(reply=f"@{login} only a maintainer can unclaim a task someone else holds.")
    holder = next((holder for holder in holders if holder.casefold() == target.casefold()), None)
    if holder is None:
        return ClaimDecision(reply=f"@{login} @{target} does not hold this task.")
    return ClaimDecision(remove=holder, react=True)


def apply_claim(decision: ClaimDecision, event: dict, github: GitHub) -> None:
    number, comment = event["issue"]["number"], event["comment"]
    repo = github.repo
    reply = decision.reply
    if decision.add:
        result = github.request("POST", f"/repos/{repo}/issues/{number}/assignees", {"assignees": [decision.add]})[0]
        if decision.add not in [assignee.get("login") for assignee in (result or {}).get("assignees", [])]:
            reply = (f"@{decision.add} GitHub would not assign you. It assigns people with access to the "
                     "repository and people who have commented on the issue; ask a maintainer to assign you.")
    if decision.remove:
        github.request("DELETE", f"/repos/{repo}/issues/{number}/assignees", {"assignees": [decision.remove]})
    if decision.react and reply is None:
        github.request("POST", f"/repos/{repo}/issues/comments/{comment['id']}/reactions", {"content": "+1"})
    if reply:
        github.request("POST", f"/repos/{repo}/issues/{number}/comments", {"body": reply})


# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    frontier = commands.add_parser("frontier", help="write the frontier of the built graph")
    frontier.add_argument("blueprint", type=Path)
    frontier.add_argument("--output", type=Path, required=True)
    frontier.add_argument("--commit", default=os.environ.get("GITHUB_SHA"))
    sync = commands.add_parser("sync", help="make the task issues match a frontier")
    sync.add_argument("frontier", type=Path)
    sync.add_argument("--repo", required=True)
    sync.add_argument("--apply", action="store_true", help="write to GitHub; without it, only report the plan")
    sync.add_argument("--max-writes", type=int, default=250)
    sync.add_argument("--pause", type=float, default=1.0, help="seconds between writes")
    sync.add_argument("--summary", type=Path, help="append a Markdown summary here (GITHUB_STEP_SUMMARY)")
    claim = commands.add_parser("claim", help="answer a /claim or /unclaim comment on a task issue")
    claim.add_argument("--event", type=Path, required=True, help="the issue_comment event (GITHUB_EVENT_PATH)")
    claim.add_argument("--repo", required=True)
    args = parser.parse_args(argv)

    if args.command == "frontier":
        result = build_frontier(args.blueprint, args.commit)
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
    api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
    if args.command == "claim":
        event = json.loads(args.event.read_text(encoding="utf-8"))
        command = claim_command(event)
        if command is None:
            print("not a claim command")
            return 0
        github = GitHub(args.repo, token, api, pause=0)
        # Decide on the issue as it is now: the event's copy predates any claim answered since. The workflow
        # answers one comment per issue at a time, so this read and the write after it do not interleave.
        number = event["issue"]["number"]
        event = dict(event, issue=github.request("GET", f"/repos/{args.repo}/issues/{number}")[0])
        maintainer = False
        verb, named = command
        login = event["comment"]["user"]["login"]
        if verb == "unclaim" and named and named.casefold() != login.casefold():
            permission = github.request("GET", f"/repos/{args.repo}/collaborators/{login}/permission")[0] or {}
            maintainer = permission.get("role_name") in MAINTAINER_ROLES or permission.get("permission") in {"admin", "write"}
        decision = decide_claim(event, maintainer)
        if decision is None:
            print("not a claim command on a task issue")
            return 0
        apply_claim(decision, event, github)
        print(decision)
        return 0
    frontier_data = json.loads(args.frontier.read_text(encoding="utf-8"))
    github = GitHub(args.repo, token, api, args.pause)
    issues = {issue["number"]: issue for label in KINDS.values() for issue in github.issues(label)}
    plan = plan_sync(frontier_data, list(issues.values()), github.labels(), args.repo)
    plan_releases(plan, list(issues.values()), github.timeline, time.time())
    applied = apply_plan(plan, github, args.repo, args.max_writes) if args.apply else None
    summary = summarize(plan, frontier_data, applied, args.max_writes)
    print(summary)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as handle:
            handle.write(summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
