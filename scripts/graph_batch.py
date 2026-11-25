#!/usr/bin/env python3
"""Make and check a graph-sync batch: the pull request that brings the wiki in step with all the Lean merged into
`main` since the last batch (docs/BLUEPRINT.md, Graph-sync batches).

    python3 scripts/graph_batch.py make [--base REV] [--bodies FILE] [--body FILE]
    python3 scripts/graph_batch.py verify [REV] [--bodies FILE]
    python3 scripts/graph_batch.py base [REV]

make runs on a clean checkout of `main` and commits the batch on top of it: one commit that changes only
scripts/taxonomy.json, scripts/wiki-sync.json, pages and folder pages under blueprint/roadmap/ and links files under
blueprint/links/. It starts from the commit the last batch brought the graph up to, which the batch commit names in its
`Graph-sync-through:` trailer, or from --base for the first batch. It first places the modules the Lean added since
then (see placement_plan): as a merged pull request's `Place:` line asks, else where the module whose declarations it
took was placed, as a proof takes its wanted statement; and it drops the place of each module that no longer exists.
It then runs `sync_wiki.py declarations` scoped to every Lean change since that commit, on main's wiki (see
synthetic_base), and checks the commit it made as verify does. --body writes a description for the pull request.

verify checks that a commit is such a batch, and exactly what make writes: its taxonomy is main's with the placement
plan applied, byte for byte, and the scoped check (`sync_wiki.py declarations --check`) finds its wiki in step, with
changes that are exactly what the sync writes, fresh article ids aside. Run it from a checkout of `main` that has the
commit the batch brought the graph up to: it runs that commit's copy of the sync.

base prints the last batch on REV (`HEAD` by default) and the commit the next batch starts from.

make and verify read the descriptions of the pull requests merged since the base with `gh`, unless --bodies gives
them as JSON ({"<number>": "<description>"}). A description is untrusted text: only its `Place:` lines are read
(see parse_place), and each counts only for a module that the pull request's own merge changed and that the taxonomy
does not place yet, under a field or subfield the taxonomy has.

Run it with a Python that has Autoform installed, as sync_wiki.py.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

if __package__:
    from . import generate_wiki as wiki
    from . import sync_wiki as sync
else:
    import generate_wiki as wiki
    import sync_wiki as sync

TAXONOMY_PATH = "scripts/taxonomy.json"
BASE_TRAILER = "Graph-sync-base"
THROUGH_TRAILER = "Graph-sync-through"
TRAILER = re.compile(rf"({BASE_TRAILER}|{THROUGH_TRAILER}): ([0-9a-f]{{40}})")
REPOSITORY = "facebookresearch/atlas-lean"
MERGE = re.compile(r"Merge pull request #(\d+) from \S+")
PLACE = re.compile(r"Place:[ \t]*(.*?)[ \t]*")
PLACE_VALUE = re.compile(r"(?P<module>\S+)[ \t]+->[ \t]+(?P<to>\S+)(?:[ \t]+\|[ \t]+(?P<title>\S.*))?")
# A placement line of scripts/taxonomy.json: two spaces, the module as a JSON string, then its entry.
PLACEMENT_LINE = re.compile(r'  ("(?:[^"\\]|\\.)*"): (\{.*\})(,?)')
MODULE = re.compile(r"[^/\s\\]+(?:/[^/\s\\]+)+")
TITLE_LIMIT = 160


class BatchError(RuntimeError):
    """What stops make or verify, said for whoever runs them."""


def git(*args: str, data: bytes | None = None) -> bytes:
    """What a git command run at the repository's root prints (see sync_wiki.git)."""
    return sync.git(*args, data=data)


def commit_of(rev: str) -> str:
    return git("rev-parse", "--verify", "--end-of-options", f"{rev}^{{commit}}").decode().strip()


def is_ancestor(older: str, newer: str) -> bool:
    return subprocess.run(["git", "-C", str(wiki.ROOT), "merge-base", "--is-ancestor", older, newer],
                          capture_output=True).returncode == 0


def blob(commit: str, path: str) -> bytes | None:
    """The bytes of the file *path* at *commit*, or None if it has none there."""
    if not git("ls-tree", "--name-only", "--full-tree", commit, "--", path).strip():
        return None
    return git("cat-file", "blob", f"{commit}:{path}")


def tree_files(commit: str) -> set[str]:
    """Every file of *commit*, by its path from the repository's root."""
    return {os.fsdecode(path) for path in git("ls-tree", "-r", "-z", "--name-only", "--full-tree", commit).split(b"\0")
            if path}


def changed_between(older: str, newer: str) -> list[str]:
    return sorted(os.fsdecode(path) for path in git("diff", "--name-only", "--no-renames", "-z", older, newer,
                                                    "--").split(b"\0") if path)


def batch_path(path: str) -> bool:
    """Whether a batch may change *path*: the taxonomy, or what the scoped sync writes (pages and folder pages, links
    files and the docstring baseline)."""
    return path == TAXONOMY_PATH or sync.written_by_sync(path)


def library_module(path: str) -> str | None:
    """The module a Lean file of one of the five libraries is, as scripts/taxonomy.json keys it, or None."""
    if path.endswith(".lean") and path.split("/", 1)[0] in wiki.LIBRARIES and "/" in path:
        return path.removesuffix(".lean")
    return None


def trailers(message: str) -> dict[str, str]:
    """The batch trailers a commit message gives, each once, or {} when one is missing or given twice."""
    found: dict[str, list[str]] = {}
    for line in message.splitlines():
        if match := TRAILER.fullmatch(line.strip()):
            found.setdefault(match.group(1), []).append(match.group(2))
    if set(found) != {BASE_TRAILER, THROUGH_TRAILER} or any(len(values) != 1 for values in found.values()):
        return {}
    return {key: values[0] for key, values in found.items()}


def batch_of(commit: str) -> tuple[str, str] | None:
    """(base, through) when *commit* is a batch: one parent, the commit its `Graph-sync-through:` trailer names; a
    `Graph-sync-base:` trailer naming an ancestor of that parent; and changes to a batch's files only."""
    parents = git("rev-list", "--parents", "-n", "1", commit).decode().split()[1:]
    found = trailers(git("log", "-1", "--format=%B", commit).decode("utf-8", "replace"))
    if len(parents) != 1 or not found or parents[0] != found[THROUGH_TRAILER]:
        return None
    if not is_ancestor(found[BASE_TRAILER], found[THROUGH_TRAILER]):
        return None
    if not all(batch_path(path) for path in changed_between(parents[0], commit)):
        return None
    return found[BASE_TRAILER], found[THROUGH_TRAILER]


def last_batch(head: str) -> tuple[str, str, str] | None:
    """The newest batch *head* contains, as (its commit, its base, the commit it brought the graph up to); each batch
    is made on a main that holds the one before, so the first in topological order is the newest."""
    listing = git("log", "--topo-order", "--format=%H", "--fixed-strings", f"--grep={THROUGH_TRAILER}: ", head)
    for commit in listing.decode().split():
        if found := batch_of(commit):
            return (commit, *found)
    return None


def merged_pull_requests(base: str, head: str) -> list[tuple[int, str]]:
    """The pull requests the merge queue merged into main after *base*, up to *head*, oldest first: each with its merge
    commit on main's first-parent history."""
    found = []
    for line in git("log", "--first-parent", "--reverse", "--format=%H %s", f"{base}..{head}").decode().splitlines():
        commit, _, subject = line.partition(" ")
        if match := MERGE.match(subject):
            found.append((int(match.group(1)), commit))
    return found


def fetch_bodies(merged: list[tuple[int, str]]) -> dict[int, str]:
    """The descriptions of the pull requests *merged*, read with `gh api graphql`, forty at a time; one whose merge
    commit is not the one main has is left out."""
    bodies: dict[int, str] = {}
    owner, name = REPOSITORY.split("/")
    for start in range(0, len(merged), 40):
        chunk = merged[start:start + 40]
        fields = " ".join(f"p{number}: pullRequest(number: {number}) {{ number body mergeCommit {{ oid }} }}"
                          for number, _ in chunk)
        query = f'query {{ repository(owner: "{owner}", name: "{name}") {{ {fields} }} }}'
        result = subprocess.run(["gh", "api", "graphql", "-f", f"query={query}"], capture_output=True, text=True)
        if result.returncode:
            raise BatchError(f"gh api graphql failed: {result.stderr.strip()}")
        found = json.loads(result.stdout)["data"]["repository"]
        for number, commit in chunk:
            pull = found.get(f"p{number}") or {}
            if (pull.get("mergeCommit") or {}).get("oid") == commit and isinstance(pull.get("body"), str):
                bodies[number] = pull["body"]
    return bodies


def read_bodies(path: Path) -> dict[int, str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not all(isinstance(value, str) for value in data.values()):
        raise BatchError(f"{path}: expected an object of pull request numbers and descriptions")
    return {int(number): body for number, body in data.items()}


def place_lines(body: str) -> list[str]:
    """The values of a description's `Place:` lines, as written."""
    return [match.group(1) for line in body.splitlines() if (match := PLACE.fullmatch(line.strip()))]


def parse_place(value: str) -> tuple[str, str, str | None]:
    """The module, field and topic title a `Place:` line gives: `<module> -> <field>`, and ` | <topic title>` after
    them when it names the topic; ValueError if it is anything else. The module is written as scripts/taxonomy.json
    keys it, a path without `.lean`, and the field as `<subject>/<field>` or `<subject>/<field>/<subfield>`."""
    match = PLACE_VALUE.fullmatch(value)
    if not match:
        raise ValueError("not `<module> -> <field>` or `<module> -> <field> | <topic title>`")
    module, to, title = match.group("module", "to", "title")
    if (not MODULE.fullmatch(module) or module.split("/", 1)[0] not in wiki.LIBRARIES
            or module.endswith(".lean")):
        raise ValueError(f"{module!r} is not a module of the five libraries, written as a path without `.lean`")
    if title is not None and (len(title) > TITLE_LIMIT or not title.isprintable()):
        raise ValueError(f"the topic title must be one line of at most {TITLE_LIMIT} printable characters")
    return module, to, title


def default_title(head: str, module: str) -> str:
    """The topic title of a module a `Place:` line names without one: its docstring's `# ` heading, as a page title,
    else its name, as generate_wiki titles a module's page."""
    text = (blob(head, f"{module}.lean") or b"").decode("utf-8", "replace")
    return wiki.page_title(wiki.module_heading(text)) or wiki.topic_title(module.rsplit("/", 1)[1])


def fields_of(taxonomy: dict) -> set[str]:
    """Every place a module may go: each subject's fields and subfields, as `<subject>/<field>[/<subfield>]`."""
    found = set()
    for subject, entry in taxonomy["subjects"].items():
        for spec in entry.get("fields", []):
            found.add(f"{subject}/{spec['slug']}")
            found.update(f"{subject}/{spec['slug']}/{sub['slug']}" for sub in spec.get("subfields", []))
    return found


def placement_of(module: str, placements: dict) -> dict | None:
    """The entry that places *module*: its own, else its nearest placed folder's (generate_wiki.placement)."""
    found = wiki.placement(tuple(module.split("/")), placements)
    return found[1] if found else None


def lean_index(commit: str):
    """Autoform's index of the Lean sources of *commit*, read from git, as the scoped sync reads a base."""
    from autoform_cli.lean import index_project

    with tempfile.TemporaryDirectory(prefix="atlas-batch-") as folder:
        root = Path(folder).resolve()
        sync.extract_tree(commit, root, sync.lean_source)
        return index_project(root, exclude_roots=sync.EXCLUDED)


@dataclass
class Placement:
    module: str
    to: str
    title: str
    # Where it comes from: a pull request's `Place:` line ("#123") or the module whose declarations it took.
    source: str


@dataclass
class PlacementPlan:
    added: list[Placement] = field(default_factory=list)
    dropped: list[str] = field(default_factory=list)
    # What an editor may want to know: `Place:` lines left out, and why; modules whose declarations came from places
    # that disagree.
    notes: list[str] = field(default_factory=list)

    def entries(self) -> dict[str, dict[str, str]]:
        return {item.module: {"to": item.to, "title": item.title} for item in self.added}


def placement_plan(base: str, head: str, bodies: dict[int, str], indexes=None) -> PlacementPlan:
    """The taxonomy changes a batch from *base* to *head* makes, before its sync.

    A module that no placement covers, neither its own nor its folder's (see placement_of), is placed:
    1. as a `Place:` line of a pull request merged in the range asks, when that pull request's merge changed the module
       and the line names a field or subfield the taxonomy has; lines that disagree about one module place it nowhere.
       A line that names no topic takes the topic of 2 when it names the same field, else the module's own title
       (default_title);
    2. else, if the module is new since *base*, where the declarations it has took their place at *base*: the module
       each of them was in at *base*, placed as the taxonomy at *head*, or else at *base*, places it, when all of them
       agree on one place and none came from an unplaced module. A proof that moves a wanted statement, with its name,
       into a new module so takes that statement's place.
    A module that no longer exists at *head*, neither as a file nor as a folder, loses its own placement. Mathlib's
    entries (`Mathlib/...`) are not the project's modules and stay. *indexes* gives the Lean indexes of *base* and
    *head* (see lean_index), read otherwise."""
    taxonomy = json.loads(blob(head, TAXONOMY_PATH))
    old = json.loads(blob(base, TAXONOMY_PATH) or b'{"placements": {}}')
    placements, old_placements, places = taxonomy["placements"], old.get("placements", {}), fields_of(taxonomy)
    files, old_files = tree_files(head), tree_files(base)
    modules = {module for path in files if (module := library_module(path))}
    old_modules = {module for path in old_files if (module := library_module(path))}
    folders = {"/".join(path.split("/")[:end]) for path in files for end in range(1, path.count("/") + 1)}
    plan = PlacementPlan()

    # 2 first, as 1 may take its topic.
    inherited: dict[str, tuple[str, str, str]] = {}
    unsure: dict[str, str] = {}
    new = sorted(module for module in modules - old_modules if placement_of(module, placements) is None)
    if new:
        old_index, index = indexes or (lean_index(base), lean_index(head))
        names: dict[str, list[str]] = {}
        for name, declaration in index.declarations.items():
            if (module := library_module(declaration.path.as_posix())) in new:
                names.setdefault(module, []).append(name)
        for module in new:
            spots, sources = set(), set()
            for name in sorted(names.get(module, [])):
                before = old_index.declarations.get(name)
                if before is None:
                    continue
                source = before.path.with_suffix("").as_posix()
                spot = placement_of(source, placements) or placement_of(source, old_placements)
                spots.add((spot["to"], spot["title"]) if spot else None)
                sources.add(source)
            if len(spots) == 1 and None not in spots:
                (to, title), = spots
                if to in places:
                    inherited[module] = (to, title, ", ".join(sorted(sources)))
                else:
                    unsure[module] = (f"{module} is left unplaced: its declarations' place, {to}, is no field or "
                                      "subfield of the taxonomy")
            elif len(spots) > 1:
                unsure[module] = (f"{module} is left unplaced: its declarations came from modules placed differently "
                                  f"or not at all ({', '.join(sorted(sources))})")

    asked: dict[str, dict[tuple[str, str], list[int]]] = {}
    for number, commit in merged_pull_requests(base, head):
        if number not in bodies:
            continue
        lines = place_lines(bodies[number])
        if not lines:
            continue
        own = {module for path in changed_between(f"{commit}^1", commit) if (module := library_module(path))}
        for value in lines:
            try:
                module, to, title = parse_place(value)
            except ValueError as error:
                plan.notes.append(f"#{number}: a `Place:` line is left out: {error}")
                continue
            if module not in modules:
                plan.notes.append(f"#{number}: {module} is left unplaced: main has no such module")
            elif module not in own:
                plan.notes.append(f"#{number}: {module} is left unplaced: the pull request's merge does not change it")
            elif to not in places:
                plan.notes.append(f"#{number}: {module} is left unplaced: {to} is no field or subfield of the taxonomy")
            elif placement_of(module, placements) is not None:
                plan.notes.append(f"#{number}: {module} keeps its place: the taxonomy already places it")
            else:
                if title is None:
                    title = (inherited[module][1] if module in inherited and inherited[module][0] == to
                             else default_title(head, module))
                asked.setdefault(module, {}).setdefault((to, title), []).append(number)
    for module, spots in sorted(asked.items()):
        if len(spots) == 1:
            (to, title), numbers = next(iter(spots.items()))
            plan.added.append(Placement(module, to, title, ", ".join(f"#{number}" for number in numbers)))
        else:
            asking = ", ".join(f"#{number}" for numbers in spots.values() for number in numbers)
            plan.notes.append(f"{module} is left unplaced: {asking} ask for different places")
    for module in new:
        if module in asked:
            continue
        if module in inherited:
            to, title, sources = inherited[module]
            plan.added.append(Placement(module, to, title, sources))
        elif module in unsure:
            plan.notes.append(unsure[module])
    plan.added.sort(key=lambda item: item.module)
    plan.dropped = sorted(key for key in placements if key.split("/", 1)[0] in wiki.LIBRARIES
                          and key not in modules and key not in folders)
    return plan


def edit_placements(text: str, added: dict[str, dict[str, str]], dropped: list[str]) -> str:
    """scripts/taxonomy.json's *text* with the placements *added* and without those *dropped*. Each added entry is one
    line, as the file writes it, right after the entry whose module comes last before its own in sorted order, or
    first if none does, as insert_rows adds a links file's rows: its place depends on the entries, not on when it is
    added. Every other line stays as it is. ValueError if the placements are not one entry per line."""
    lines = text.split("\n")
    try:
        start = lines.index(' "placements": {')
        end = next(number for number in range(start + 1, len(lines)) if lines[number] in (" }", " },"))
    except (ValueError, StopIteration):
        raise ValueError("scripts/taxonomy.json has no placements block of one entry per line") from None
    entries = []
    for line in lines[start + 1:end]:
        match = PLACEMENT_LINE.fullmatch(line)
        if not match:
            raise ValueError(f"scripts/taxonomy.json: not a placement line: {line[:80]}")
        entries.append((json.loads(match.group(1)), f"  {match.group(1)}: {match.group(2)}"))
    keys = {key for key, _ in entries}
    if overlap := sorted(keys & set(added)):
        raise ValueError(f"already placed: {', '.join(overlap)}")
    if missing := sorted(set(dropped) - keys):
        raise ValueError(f"no such placement: {', '.join(missing)}")
    kept = [(key, line) for key, line in entries if key not in set(dropped)]
    for key, spot in sorted(added.items()):
        line = f"  {json.dumps(key, ensure_ascii=False)}: {json.dumps(spot, ensure_ascii=False)}"
        at = max(((other, number) for number, (other, _) in enumerate(kept) if other < key), default=(None, -1))[1]
        kept.insert(at + 1, (key, line))
    body = [line + ("," if number < len(kept) - 1 else "") for number, (_, line) in enumerate(kept)]
    edited = "\n".join(lines[:start + 1] + body + lines[end:])
    before, after = json.loads(text), json.loads(edited)
    expected = {key: value for key, value in before["placements"].items() if key not in set(dropped)} | added
    if after["placements"] != expected or {**after, "placements": None} != {**before, "placements": None}:
        raise ValueError("editing the placements changed something else")
    return edited


def synthetic_base(base: str, head: str, taxonomy: str) -> str:
    """A commit that has *head*'s tree, but the Lean sources of *base* and the taxonomy blob *taxonomy*: the scoped
    sync run from it takes every Lean change from *base* to *head* as its own, on *head*'s wiki and baseline, read with
    the taxonomy the batch writes. It is a local commit, never pushed."""
    with tempfile.TemporaryDirectory(prefix="atlas-batch-index-") as folder:
        environment = {**os.environ, "GIT_INDEX_FILE": str(Path(folder) / "index")}

        def run(*args: str, data: bytes | None = None) -> bytes:
            return subprocess.run(["git", "-C", str(wiki.ROOT), *args], input=data, env=environment,
                                  capture_output=True, check=True).stdout

        run("read-tree", head)
        raw = run("diff", "--raw", "--no-renames", "-z", "--no-abbrev", base, head, "--").split(b"\0")
        entries = []
        for meta, path in zip(raw[0::2], raw[1::2]):
            name = os.fsdecode(path)
            if not meta.startswith(b":") or not sync.lean_source(name):
                continue
            mode, _, sha = meta[1:].decode("ascii").split(" ")[:3]
            entries.append(f"{mode} {sha}\t{name}" if mode != "000000" else f"0 {'0' * 40}\t{name}")
        if entries:
            run("update-index", "-z", "--index-info", data="".join(f"{entry}\0" for entry in entries).encode())
        run("update-index", "--cacheinfo", f"100644,{taxonomy},{TAXONOMY_PATH}")
        tree = run("write-tree").decode().strip()
    return git("commit-tree", tree, "-p", head, "-m", f"The tree of {head} with the Lean of {base}").decode().strip()


def run_sync(root: Path, base: str, report: Path, check: bool) -> tuple[int, str]:
    """Run *root*'s copy of `sync_wiki.py declarations --base BASE` (with --check when *check*), its output kept."""
    command = [sys.executable, str(root / "scripts" / "sync_wiki.py"), "declarations", "--base", base,
               "--report", str(report)] + (["--check"] if check else [])
    result = subprocess.run(command, cwd=root, capture_output=True, text=True)
    return result.returncode, result.stdout + result.stderr


def status_paths() -> list[str]:
    """What the working tree and the index change from HEAD, untracked files included, by path."""
    found = git("status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none").split(b"\0")
    paths, skip = [], False
    for record in found:
        if skip:
            skip = False
            continue
        if record:
            paths.append(os.fsdecode(record[3:]))
            skip = record[:1] in (b"R", b"C")
    return sorted(paths)


def bodies_for(base: str, head: str, path: Path | None) -> dict[int, str]:
    return read_bodies(path) if path else fetch_bodies(merged_pull_requests(base, head))


def message_for(base: str, head: str, plan: PlacementPlan, report: dict) -> str:
    """The batch commit's message, with the trailers that name its base and the commit it brings the graph up to."""
    summary = (f"Pages for the {len(report.get('missing', []))} documented declarations that the Lean merged into main "
               f"after {base[:12]}, up to {head[:12]}, left without one; {len(plan.added)} modules placed and "
               f"{len(plan.dropped)} placements of modules that no longer exist dropped. Made by "
               "scripts/graph_batch.py make.")
    return "\n".join([f"Sync the graph with the Lean merged up to {head[:12]}", "", textwrap.fill(summary, 72), "",
                      f"{BASE_TRAILER}: {base}", f"{THROUGH_TRAILER}: {head}", ""])


def make(options) -> int:
    head = commit_of("HEAD")
    if left := status_paths():
        raise BatchError(f"make needs a clean checkout of main; it has changes: {', '.join(left[:5])}")
    if options.base:
        base = commit_of(options.base)
    elif found := last_batch(head):
        base = found[2]
    else:
        raise BatchError("no batch on this branch yet: give the first batch's base with --base")
    if base == head or not is_ancestor(base, head):
        raise BatchError(f"{base} is not an older commit of this branch")
    print(f"Batch from {base} up to {head}.", flush=True)
    bodies = bodies_for(base, head, options.bodies)
    indexes = (lean_index(base), lean_index(head))
    plan = placement_plan(base, head, bodies, indexes)
    taxonomy = wiki.ROOT / TAXONOMY_PATH
    taxonomy.write_text(edit_placements(taxonomy.read_text(encoding="utf-8"), plan.entries(), plan.dropped),
                        encoding="utf-8")
    written = git("hash-object", "-w", "--", TAXONOMY_PATH).decode().strip()
    synthetic = synthetic_base(base, head, written)
    with tempfile.TemporaryDirectory(prefix="atlas-batch-report-") as folder:
        report_path = Path(folder) / "report.json"
        status, output = run_sync(wiki.ROOT, synthetic, report_path, check=False)
        report = json.loads(report_path.read_text()) if report_path.is_file() else {}
    if status:
        raise BatchError("the sync stopped, and nothing is committed; `git reset --hard` and `git clean -fd blueprint` "
                         "restore the checkout. Its output:\n" + output)
    changed = status_paths()
    if stray := [path for path in changed if not batch_path(path)]:
        raise BatchError(f"the run changed files a batch never changes: {', '.join(stray)}")
    if not changed:
        print("Nothing to sync: the graph is in step with the Lean merged up to here.")
        return 0
    git("add", "-A", "--", TAXONOMY_PATH, "scripts/wiki-sync.json", "blueprint/roadmap", "blueprint/links")
    git("commit", "-q", "--no-verify", "-F", "-", data=message_for(base, head, plan, report).encode())
    commit = commit_of("HEAD")
    print(f"Committed the batch as {commit}.", flush=True)
    verify_commit(commit, bodies, plan=plan)
    if options.body:
        options.body.write_text(describe(commit, base, head, plan, report), encoding="utf-8")
    return 0


@dataclass
class Verdict:
    base: str
    through: str
    report: dict


def verify_commit(commit: str, bodies: dict[int, str], plan: PlacementPlan | None = None,
                  onto: str | None = None) -> Verdict:
    """Check that *commit* is a batch, and exactly what make writes (see the module docstring), and, given a newer main
    *onto*, that it still merges cleanly into it and that the scoped check finds nothing the merge breaks there, such as
    a second page for a declaration or a link to one main no longer has; BatchError otherwise."""
    found = batch_of(commit)
    if found is None:
        raise BatchError(f"{commit} is not a batch: one commit on the commit its {THROUGH_TRAILER} trailer names, "
                         f"with a {BASE_TRAILER} trailer naming an older commit, that changes only a batch's files")
    base, through = found
    if not is_ancestor(through, commit_of("HEAD")):
        raise BatchError(f"run verify from a checkout of main that has {through}: it runs that commit's sync")
    plan = plan or placement_plan(base, through, bodies)
    expected = edit_placements(blob(through, TAXONOMY_PATH).decode("utf-8"), plan.entries(), plan.dropped)
    actual = (blob(commit, TAXONOMY_PATH) or b"").decode("utf-8")
    if expected != actual:
        raise BatchError("the batch's scripts/taxonomy.json is not main's with the placement plan applied")
    taxonomy = git("rev-parse", f"{commit}:{TAXONOMY_PATH}").decode().strip()
    synthetic = synthetic_base(base, through, taxonomy)
    merged = None
    if onto is not None:
        result = subprocess.run(["git", "-C", str(wiki.ROOT), "merge-tree", "--write-tree", "--no-messages", onto,
                                 commit], capture_output=True, text=True)
        if result.returncode:
            raise BatchError(f"the batch no longer merges cleanly into {onto}: make a new batch from a fresh main")
        merged = git("commit-tree", result.stdout.split()[0], "-p", onto, "-p", commit, "-m",
                     f"The batch {commit} merged into {onto}").decode().strip()
    with tempfile.TemporaryDirectory(prefix="atlas-batch-verify-") as folder:
        tree, report_path = Path(folder) / "tree", Path(folder) / "report.json"
        git("worktree", "add", "-q", "--detach", str(tree), commit)
        try:
            status, output = run_sync(tree, synthetic, report_path, check=True)
            report = json.loads(report_path.read_text()) if report_path.is_file() else {}
            if report.get("in_step") is not True or report.get("wiki_changes") not in ("sync", "none"):
                raise BatchError("the scoped check does not find the batch's wiki exactly the sync's, in step. Its "
                                 "output:\n" + output)
            if merged is not None:
                subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--detach", merged], check=True,
                               capture_output=True)
                status, output = run_sync(tree, onto, report_path, check=True)
                onto_report = json.loads(report_path.read_text()) if report_path.is_file() else {}
                if onto_report.get("in_step") is not True:
                    raise BatchError(f"merged into {onto}, the batch breaks what the scoped check reads: make a new "
                                     "batch from a fresh main. Its output:\n" + output)
        finally:
            git("worktree", "remove", "--force", str(tree))
    print(f"{commit} is the batch from {base} up to {through}: its taxonomy is main's with the placement plan "
          "applied, and its wiki is in step, exactly what the sync writes."
          + (f" It merges cleanly into {onto}, and the scoped check finds nothing the merge breaks." if onto else ""))
    return Verdict(base, through, report)


def describe(commit: str, base: str, head: str, plan: PlacementPlan, report: dict) -> str:
    """A description for the batch's pull request, in Markdown."""
    missing = report.get("missing", [])
    modules: dict[str, int] = {}
    for key in missing:
        modules[report["new"][key]] = modules.get(report["new"][key], 0) + 1
    written = report.get("written", [])
    folders = sum(1 for path in written if path.startswith("blueprint/roadmap/") and path.endswith("README.md"))
    unrecorded = [page for page in report.get("changed", []) if page.split(" (", 1)[0] in report.get("digests", {})]
    lines = ["Graph: batch", "",
             f"Pages for the documented declarations that the Lean merged into `main` after `{base}`, up to `{head}`, "
             "left without one, made by `scripts/graph_batch.py make` "
             "([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)).", "",
             f"- {len(missing)} new pages, for declarations of {len(modules)} modules; {folders} folder pages written "
             f"or extended; {len(report.get('digests', {}))} docstring digests written.",
             f"- {len(plan.added)} modules placed in `scripts/taxonomy.json`, {len(plan.dropped)} placements of modules "
             "that no longer exist dropped.", ""]
    if plan.added:
        lines += ["### Placements", "", "| Module | Field | Topic | From |", "| --- | --- | --- | --- |"]
        lines += [f"| `{item.module}` | `{item.to}` | {item.title} | {item.source} |" for item in plan.added]
        lines.append("")
    if plan.dropped:
        lines += ["### Placements dropped", ""] + [f"- `{key}`" for key in plan.dropped] + [""]
    if plan.notes:
        lines += ["### Left for an editor", ""] + [f"- {note}" for note in plan.notes] + [""]
    if unrecorded:
        lines += ["### Pages to check", "", "Their declaration's docstring changed, and no pull request recorded the "
                  "new digest:", ""] + [f"- {page}" for page in unrecorded] + [""]
    for title, key in (("Held back, so with no page", "held"), ("Listed as duplicates, so with no page", "duplicates"),
                       ("Documented declarations the Lean index lacks", "unindexed")):
        if report.get(key):
            lines += [f"### {title}", ""] + [f"- {row}" for row in report[key]] + [""]
    lines += ["### New pages by module", ""] + [f"- `{module}`: {count}" for module, count in sorted(modules.items())]
    lines += ["", "## Validation", "",
              f"- `python3 scripts/graph_batch.py verify {commit}`, from a checkout of `main` that has `{head}`: the "
              "taxonomy is main's with the placement plan applied, and the scoped check finds the wiki in step, "
              "exactly what the sync writes."]
    return "\n".join(lines) + "\n"


def run_verify(options) -> int:
    commit = commit_of(options.commit)
    found = batch_of(commit)
    if found is None:
        raise BatchError(f"{commit} is not a batch: one commit on the commit its {THROUGH_TRAILER} trailer names, "
                         f"with a {BASE_TRAILER} trailer naming an older commit, that changes only a batch's files")
    head = commit_of("HEAD")
    # From a newer main, the batch must still merge into it as it is.
    onto = head if head not in (commit, found[1]) and not is_ancestor(head, commit) else None
    verify_commit(commit, bodies_for(*found, options.bodies), onto=onto)
    return 0


def run_base(options) -> int:
    head = commit_of(options.rev)
    if found := last_batch(head):
        commit, base, through = found
        print(f"Last batch: {commit}, from {base} up to {through}.")
        print(f"The next batch starts from {through}.")
        return 0
    print("No batch on this branch yet: the first batch takes its base from --base.")
    return 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="graph_batch.py", description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    making = commands.add_parser("make", help="commit the next batch on a clean checkout of main")
    making.add_argument("--base", metavar="REV", help="the first batch's base; later ones take the last batch's")
    making.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    making.add_argument("--body", type=Path, metavar="FILE", help="write a description for the pull request")
    verifying = commands.add_parser("verify", help="check that a commit is exactly the batch make writes")
    verifying.add_argument("commit", nargs="?", default="HEAD", metavar="REV")
    verifying.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    basing = commands.add_parser("base", help="print the last batch and where the next one starts")
    basing.add_argument("rev", nargs="?", default="HEAD", metavar="REV")
    options = parser.parse_args(argv)
    try:
        return {"make": make, "verify": run_verify, "base": run_base}[options.command](options)
    except (BatchError, sync.GitError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        print(f"error: {' '.join(error.cmd)} failed: {(error.stderr or b'').decode('utf-8', 'replace').strip()}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
