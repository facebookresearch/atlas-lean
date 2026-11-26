#!/usr/bin/env python3
"""Make and check a graph-sync batch: the pull request that brings the wiki in step with all the Lean merged into
`main` since the last batch (docs/BLUEPRINT.md, Graph-sync batches).

    python3 scripts/graph_batch.py make [--base REV] [--bodies FILE] [--body FILE]
    python3 scripts/graph_batch.py verify REV [--bodies FILE] [--body FILE]
    python3 scripts/graph_batch.py base [REV]

make runs on a clean checkout of `main` and commits the batch on top of it: one commit that changes only
scripts/taxonomy.json, scripts/wiki-sync.json, pages and folder pages under blueprint/roadmap/ and links files under
blueprint/links/. It starts from the commit the last batch brought the graph up to, which the batch commit names in its
`Graph-sync-through:` trailer, or from --base, which may start earlier, never later. It first places the modules the
Lean added since then that nothing places (see placement_plan): as a merged pull request's `Place:` line asks, else
where the module whose declarations it took was placed, as a proof takes its wanted statement; and it drops the place
of each module that no longer exists. It then runs `sync_wiki.py declarations` scoped to every Lean change since that
commit, on main's wiki (see synthetic_base), and checks the commit it made as verify does. --body writes a description
for the pull request.

verify checks that a commit is such a batch, made on main's first-parent history, starting no later than where the
last batch before it ended, and exactly what make writes: its taxonomy is main's with the placement plan applied, byte
for byte, and the scoped check (`sync_wiki.py declarations --check`) finds its wiki in step, with changes that are
exactly what the sync writes, fresh article ids aside. Run it from an up-to-date checkout of `main`: it runs the sync of
the commit the batch was made on, which must be one of main's own states; from a newer main, it also checks that the
batch still merges into it cleanly and that the scoped check finds nothing the merge breaks. It then prints the
description it recomputes, which the batch's reviewer reads instead of the pull request's (--body writes it too).

base prints the last batch on REV (`HEAD` by default) and the commit the next batch starts from.

make and verify read the descriptions of the pull requests merged since the base with `gh`, unless --bodies gives
them as JSON (see read_bodies). A description is untrusted text: only its `Place:` lines are read, those GitHub's
rendering shows as lines of plain text (visible_lines), none of a description edited after the merge or given with no
rendering (see parse_place); each counts only for a module that the pull request's own merge changed, that no
placement covers and that has no page outside that topic yet, under a field or subfield the taxonomy has.

Run it with a Python that has Autoform installed, as sync_wiki.py.
"""

from __future__ import annotations

import argparse
import functools
import html.parser
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
# The first line of a batch commit's message, followed by the first 12 digits of the commit it was made on.
SUBJECT = "Sync the graph with the Lean merged up to "
REPOSITORY = "facebookresearch/atlas-lean"
MERGE = re.compile(r"Merge pull request #(\d+) from \S+")
PLACE = re.compile(r"Place:[ \t]*(.*?)[ \t]*")
# The opening of a fenced code block: at most three spaces, then a run of three or more backticks or tildes.
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
PLACE_VALUE = re.compile(r"(?P<module>\S+)[ \t]+->[ \t]+(?P<to>\S+)(?:[ \t]+\|[ \t]+(?P<title>\S.*))?")
# The first line of a placement entry of scripts/taxonomy.json: two spaces, then the module as a JSON string.
PLACEMENT_START = re.compile(r'  "(?:[^"\\]|\\.)*": ')
# A module of the five libraries, as scripts/taxonomy.json keys it: a path of Lean identifiers, without `.lean`.
MODULE = re.compile(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)+")
TITLE_LIMIT = 160
# What a topic title from a description may not hold: Markdown and HTML that the site, a folder page or the batch's
# description would read as more than text, and GitHub's mentions and references.
UNSAFE = set("<>[]{}|`\\@#")
# Module names that say nothing of a module's topic: a topic titled after the folder holding them instead.
GENERIC = {"Basic", "Defs", "Lemmas", "Main", "Core", "Instances", "Results", "Theorems", "Statement", "Statements",
           "Definitions", "Properties", "Wanted"}
# The sync's report sections (sync_wiki.REPORT) that ask an editor for something, by kind.
EDITOR_ITEMS = ("parts", "replaced", "appended", "unlisted", "unassigned", "unindexed", "stale_duplicates")
# The identity and date of the commits made only to compare with (synthetic_base, verify_commit's merge), never pushed:
# fixed, so that they need no configured identity and the same inputs give the same commits.
LOCAL_IDENTITY = {"GIT_AUTHOR_NAME": "graph_batch.py", "GIT_AUTHOR_EMAIL": "graph-batch@example.invalid",
                  "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z", "GIT_COMMITTER_NAME": "graph_batch.py",
                  "GIT_COMMITTER_EMAIL": "graph-batch@example.invalid", "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z"}


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


@functools.cache
def mainline(head: str) -> frozenset[str]:
    """The commits of *head*'s first-parent history: the states `main` has had, each one checked as a whole by the
    merge queue, unlike the commits of a merged pull request's branch."""
    return frozenset(git("rev-list", "--first-parent", head).decode().split())


def blob(commit: str, path: str) -> bytes | None:
    """The bytes of the file *path* at *commit*, or None if it has none there."""
    if not git("ls-tree", "--name-only", "--full-tree", commit, "--", path).strip():
        return None
    return git("cat-file", "blob", f"{commit}:{path}")


def tree_files(commit: str, *paths: str) -> set[str]:
    """Every file of *commit*, or those under *paths*, by its path from the repository's root."""
    listing = git("ls-tree", "-r", "-z", "--name-only", "--full-tree", commit, "--", *paths)
    return {os.fsdecode(path) for path in listing.split(b"\0") if path}


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


def batch_of(commit: str, head: str) -> tuple[str, str] | None:
    """(base, through) when *commit* is a batch for the `main` whose tip is *head*: one commit, whose message make
    wrote (SUBJECT, then the two trailers), on the commit its `Graph-sync-through:` trailer names, with a
    `Graph-sync-base:` trailer naming an older commit, both of them on *head*'s first-parent history (mainline), that
    changes a batch's files and nothing else."""
    parents = git("rev-list", "--parents", "-n", "1", commit).decode().split()[1:]
    message = git("log", "-1", "--format=%B", commit).decode("utf-8", "replace")
    found = trailers(message)
    if len(parents) != 1 or not found or parents[0] != found[THROUGH_TRAILER]:
        return None
    base, through = found[BASE_TRAILER], found[THROUGH_TRAILER]
    if message.splitlines()[0] != f"{SUBJECT}{through[:12]}":
        return None
    if base not in mainline(head) or through not in mainline(head) or not is_ancestor(base, through):
        return None
    changed = changed_between(through, commit)
    if not changed or not all(batch_path(path) for path in changed):
        return None
    return base, through


@functools.cache
def merged_heads(head: str) -> frozenset[str]:
    """The heads of the pull requests merged into *head*'s first-parent history, which their reviews covered: the
    second parents of its merges, not the commits within a merged branch."""
    lines = git("rev-list", "--first-parent", "--merges", "--parents", head).decode().splitlines()
    return frozenset(parts[2] for parts in (line.split() for line in lines) if len(parts) > 2)


def last_batch(head: str) -> tuple[str, str, str] | None:
    """The newest batch merged into *head*, as (its commit, its base, the commit it brought the graph up to): the head
    of a merged pull request (merged_heads) that is a batch (batch_of). Each batch is made on a main that holds the one
    before, so the first in topological order is the newest."""
    listing = git("log", "--topo-order", "--format=%H", "--fixed-strings", f"--grep={THROUGH_TRAILER}: ", head)
    for commit in listing.decode().split():
        if commit in merged_heads(head) and (found := batch_of(commit, head)):
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


class Body(str):
    """A merged pull request's description; whether it was edited after the merge (*edited*), when its `Place:` lines
    are left out, as no review of the merge saw them; and GitHub's rendering of it (*html*), when known, of which only
    the lines it shows as plain text count (visible_lines)."""
    edited: bool = False
    html: str | None = None


def body(text: str, edited: bool = False, rendered: str | None = None) -> Body:
    value = Body(text)
    value.edited, value.html = edited, rendered
    return value


def fetch_bodies(merged: list[tuple[int, str]]) -> dict[int, Body]:
    """The descriptions of the pull requests *merged*, read with `gh api graphql`, forty at a time, each marked when it
    was edited after the merge; one whose merge commit is not the one main has is left out."""
    bodies: dict[int, Body] = {}
    owner, name = REPOSITORY.split("/")
    for start in range(0, len(merged), 40):
        chunk = merged[start:start + 40]
        fields = " ".join(f"p{number}: pullRequest(number: {number}) {{ number body bodyHTML mergedAt lastEditedAt "
                          "mergeCommit { oid } }" for number, _ in chunk)
        query = f'query {{ repository(owner: "{owner}", name: "{name}") {{ {fields} }} }}'
        try:
            result = subprocess.run(["gh", "api", "graphql", "-f", f"query={query}"], capture_output=True, text=True)
        except FileNotFoundError:
            raise BatchError("reading the pull requests' descriptions needs `gh`, logged in; or give them with "
                             "--bodies") from None
        if result.returncode:
            raise BatchError(f"gh api graphql failed: {result.stderr.strip()}")
        found = json.loads(result.stdout)["data"]["repository"]
        for number, commit in chunk:
            pull = found.get(f"p{number}") or {}
            if (pull.get("mergeCommit") or {}).get("oid") == commit and isinstance(pull.get("body"), str):
                edited, merged_at = pull.get("lastEditedAt"), pull.get("mergedAt")
                rendered = pull.get("bodyHTML") if isinstance(pull.get("bodyHTML"), str) else ""
                bodies[number] = body(pull["body"], bool(edited and merged_at and edited > merged_at), rendered)
    return bodies


def read_bodies(path: Path) -> dict[int, Body]:
    """Descriptions given as JSON: {"<number>": {"body": "<description>", "html": "<GitHub's rendering>", "edited":
    true}}, "edited" for one edited after the merge. A description given with no rendering ({"<number>":
    "<description>"}, or no "html") places nothing: only the rendering says which lines GitHub shows."""
    data = json.loads(path.read_text(encoding="utf-8"))
    bodies = {}
    for number, value in (data.items() if isinstance(data, dict) else []):
        if isinstance(value, dict) and isinstance(value.get("body"), str):
            rendered = value.get("html") if isinstance(value.get("html"), str) else None
            bodies[int(number)] = body(value["body"], value.get("edited") is True, rendered)
        elif isinstance(value, str):
            bodies[int(number)] = body(value)
        else:
            raise BatchError(f"{path}: expected an object of pull request numbers and descriptions")
    if not isinstance(data, dict):
        raise BatchError(f"{path}: expected an object of pull request numbers and descriptions")
    return bodies


def place_lines(text: str) -> list[str]:
    """The values of a description's `Place:` lines, read from its Markdown, for the notes on lines GitHub's rendering
    does not show (visible_lines reads that, and only it counts): lines of their own, as Markdown ends lines (at a line
    feed or a carriage return only), indented by less than four columns, outside fenced code blocks and HTML comments,
    which the rendered description does not show as text. A fence closes only on a line of at most three spaces, a run
    of its own character at least as long, and nothing after it but spaces and tabs; a line holding `<!--` anywhere
    opens a comment that runs to the next `-->`."""
    found, fence, comment = [], None, False
    for line in re.split(r"\r\n|\r|\n", text):
        if comment:
            comment = "-->" not in line
            continue
        if fence:
            if re.fullmatch(rf" {{0,3}}{re.escape(fence[0])}{{{len(fence)},}}[ \t]*", line):
                fence = None
            continue
        if match := FENCE.match(line):
            fence = match.group(1)
            continue
        if "<!--" in line:
            comment = "-->" not in line[line.index("<!--") + 4:]
            continue
        if line.expandtabs(4)[:4] == "    ":
            continue  # An indented code block, or a line too deep to be one of its own.
        if match := PLACE.fullmatch(line.strip(" \t")):
            found.append(match.group(1))
    return found


# Elements that hold no content and have no end tag.
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}


class VisibleLines(html.parser.HTMLParser):
    """The lines of plain text of a rendered description's top-level paragraphs, split at `<br>`: what GitHub shows as
    lines of their own. A line that holds any element (a link, code, emphasis, an image), or that an element spans,
    is left out, as is everything in another element: a list, a quotation, a table, a code block, a `<details>`."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.lines: list[str] = []
        self.depth, self.inner, self.paragraph, self.tainted, self.current = 0, 0, False, False, []

    def flush(self) -> None:
        text = "".join(self.current).strip(" \t\n")
        if text and not self.tainted:
            self.lines.append(text)
        self.current, self.tainted = [], self.inner > 0

    def handle_starttag(self, tag: str, attrs) -> None:
        if self.paragraph:
            if tag == "br":
                self.flush()
                return
            self.tainted = True
            self.inner += tag not in VOID
        elif tag == "p" and self.depth == 0:
            self.paragraph, self.inner, self.tainted, self.current = True, 0, False, []
        elif tag not in VOID:
            self.depth += 1

    def handle_startendtag(self, tag: str, attrs) -> None:
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag: str) -> None:
        if self.paragraph:
            if tag == "p" and self.inner == 0:
                self.flush()
                self.paragraph = False
            elif tag not in VOID and self.inner:
                self.inner -= 1
        elif tag not in VOID and self.depth:
            self.depth -= 1

    def handle_data(self, data: str) -> None:
        if self.paragraph:
            self.current.append(data)


def visible_lines(rendered: str) -> list[str]:
    """The values of the `Place:` lines that GitHub's rendering of a description shows as lines of plain text in a
    top-level paragraph (VisibleLines)."""
    parser = VisibleLines()
    parser.feed(rendered)
    parser.close()
    return [match.group(1) for line in parser.lines if (match := PLACE.fullmatch(line))]


def placed_module(value: str) -> str | None:
    """The module a `Place:` line's value names, or None if it names none (parse_place)."""
    try:
        return parse_place(value)[0]
    except ValueError:
        return None


def parse_place(value: str) -> tuple[str, str, str | None]:
    """The module, field and topic title a `Place:` line gives: `<module> -> <field>`, and ` | <topic title>` after
    them when it names the topic; ValueError if it is anything else. The module is written as scripts/taxonomy.json
    keys it, a path of Lean identifiers without `.lean`, and the field as `<subject>/<field>` or
    `<subject>/<field>/<subfield>`. A title is one line of at most TITLE_LIMIT printable characters, none of UNSAFE,
    with no address (`://`), which GitHub would read as a reference.
    The error never repeats the line's text, which is untrusted."""
    match = PLACE_VALUE.fullmatch(value)
    if not match:
        raise ValueError("it is not `<module> -> <field>` or `<module> -> <field> | <topic>`")
    module, to, title = match.group("module", "to", "title")
    if not MODULE.fullmatch(module) or module.split("/", 1)[0] not in wiki.LIBRARIES:
        raise ValueError("it names no module of the five libraries, as a path without `.lean`")
    if title is not None and (len(title) > TITLE_LIMIT or not title.isprintable() or UNSAFE & set(title)
                              or "://" in title):
        raise ValueError(f"its topic is not one line of at most {TITLE_LIMIT} printable characters free of "
                         f"{''.join(sorted(UNSAFE))} and of addresses")
    return module, to, title


def default_title(head: str, module: str) -> str:
    """The topic title of a module a `Place:` line names without one: its docstring's `# ` heading, as a page title,
    else its name, as generate_wiki titles a module's page, or, for a name that says nothing (GENERIC), its folder's."""
    text = (blob(head, f"{module}.lean") or b"").decode("utf-8", "replace")
    *folder, name = module.split("/")
    return (wiki.page_title(wiki.module_heading(text))
            or wiki.topic_title(folder[-1] if name in GENERIC and len(folder) > 1 else name))


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


def subject_of(module: str, taxonomy: dict) -> str | None:
    """The subject an unplaced module's pages go under, in its `not-yet-classified/` folder, as generate_wiki takes it
    from its library's folder; None when the taxonomy has no such subject, and the module gets no pages."""
    library, folder = module.split("/")[:2]
    subject = wiki.LIBRARIES[library].get(folder, folder)
    return subject if subject in taxonomy["subjects"] else None


def lean_index(commit: str):
    """Autoform's index of the Lean sources of *commit*, read from git, as the scoped sync reads a base."""
    from autoform_cli.lean import index_project

    with tempfile.TemporaryDirectory(prefix="atlas-batch-") as folder:
        root = Path(folder).resolve()
        sync.extract_tree(commit, root, sync.lean_source)
        return index_project(root, exclude_roots=sync.EXCLUDED)


def in_topic(page: str, to: str, title: str) -> bool:
    """Whether a page, by path from the roadmap, sits where the placement (*to*, *title*) lays out its module's pages
    (generate_wiki.topic_node): in the topic's folder, or right in the field for a topic of one page, either of them
    possibly within one of the field's parts."""
    if not page.startswith(f"{to}/"):
        return False
    rest = page[len(to) + 1:].split("/")
    if len(rest) > 1 and re.fullmatch(r"part-\d+", rest[0]):
        rest = rest[1:]
    return len(rest) == 1 or rest[0] == wiki.slugify(title)


def module_pages(head: str, index) -> dict[str, set[str]]:
    """The pages that already stand for a declaration of each module at *head*, by path from the roadmap: those whose
    row links the declaration, holds it back or lists it as a duplicate, read as the sync reads rows."""
    pages: dict[str, set[str]] = {}
    for path in sorted(tree_files(head, "blueprint/links")):
        if not sync.LINKS_FILE.fullmatch(path):
            continue
        try:
            rows = sync.read_rows(blob(head, path).decode("utf-8"))
        except ValueError:
            continue  # The sync stops on such a file itself.
        for row in rows:
            if not isinstance(row, dict):
                continue
            try:
                names = {name for name in (sync.lean_name(row), sync.held_name(row)) if name}
                names.update(sync.duplicate_names(row))
                legacy = sync.legacy_pair(row)
                page = sync.page_name(row) if names or legacy else None
            except (ValueError, TypeError, AttributeError, KeyError):
                continue
            modules = {library_module(declaration.path.as_posix()) for name in names
                       if (declaration := index.declarations.get(name)) is not None}
            if legacy:
                # A row an earlier sync wrote with only a module and a name.
                modules.add(library_module(legacy[0].replace(".", "/") + ".lean"))
            for module in modules - {None}:
                pages.setdefault(module, set()).add(page)
    return pages


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
    # The modules new since the base that stay unplaced, each with where its pages go: its subject's
    # `not-yet-classified/` folder, or nowhere for a folder with no subject.
    unplaced: list[tuple[str, str | None]] = field(default_factory=list)
    # The older modules a pull request in the range changed that get no pages, in a folder that is no subject.
    subjectless: list[str] = field(default_factory=list)
    # What an editor may want to know: `Place:` lines left out, and why; modules whose declarations came from places
    # that disagree; modules that already have pages.
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
    A placement never contradicts where a module's pages already are (see module_pages, in_topic): the sync moves no
    page, so a module with a page outside the topic it would get is noted and left as it is, for a graph pull request
    that moves its pages too; a proof's module, whose moved statement's page is already in that topic, is placed. A
    changed module that gets no pages, in a folder that is no subject, is listed (PlacementPlan.subjectless), and such
    a module older than the base is never placed: the scoped sync would give pages only to its new declarations. A
    `Place:` line of a description edited after the merge, or one GitHub does not show as a line of plain text, is left
    out, with a note (Body, visible_lines). A module that no
    longer exists at *head*, neither as a file nor as a folder, loses its own placement. Mathlib's entries
    (`Mathlib/...`) are not the project's modules and stay. *indexes* gives the Lean indexes of *base* and *head* (see
    lean_index), read otherwise."""
    taxonomy = json.loads(blob(head, TAXONOMY_PATH))
    old = json.loads(blob(base, TAXONOMY_PATH) or b'{"placements": {}}')
    placements, old_placements, places = taxonomy["placements"], old.get("placements", {}), fields_of(taxonomy)
    files, old_files = tree_files(head), tree_files(base)
    modules = {module for path in files if (module := library_module(path))}
    old_modules = {module for path in old_files if (module := library_module(path))}
    folders = {"/".join(path.split("/")[:end]) for path in files for end in range(1, path.count("/") + 1)}
    plan = PlacementPlan()

    @functools.cache
    def read_indexes():
        return indexes or (lean_index(base), lean_index(head))

    @functools.cache
    def pages() -> dict[str, set[str]]:
        return module_pages(head, read_indexes()[1])

    # 2 first, as 1 may take its topic.
    inherited: dict[str, tuple[str, str, str]] = {}
    unsure: dict[str, str] = {}
    new = sorted(module for module in modules - old_modules if placement_of(module, placements) is None)
    if new:
        old_index, index = read_indexes()
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
        # Only GitHub's rendering says which lines it shows as plain text; the Markdown's reading serves the notes.
        rendered = getattr(bodies[number], "html", None)
        written = place_lines(bodies[number])
        lines = visible_lines(rendered) if rendered is not None else []
        if not lines and not written:
            continue
        if getattr(bodies[number], "edited", False):
            plan.notes.append(f"#{number}: its `Place:` lines are left out: its description was edited after the merge")
            continue
        if rendered is None:
            plan.notes.append(f"#{number}: its `Place:` lines are left out: its rendering is not known")
            continue
        shown = {placed_module(value) for value in lines}
        if hidden := [value for value in written if (module := placed_module(value)) and module not in shown]:
            plan.notes.append(f"#{number}: {len(hidden)} `Place:` line(s) left out: GitHub does not show them as "
                              "lines of plain text")
        own = {module for path in changed_between(f"{commit}^1", commit) if (module := library_module(path))}
        for value in lines:
            try:
                module, to, title = parse_place(value)
            except ValueError as error:
                plan.notes.append(f"#{number}: a `Place:` line is left out: {error}")
                continue
            if module not in modules:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: main has no such module")
            elif module not in own:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: the pull request's merge does not change it")
            elif to not in places:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: its line names no field or subfield of the "
                                  "taxonomy")
            elif placement_of(module, placements) is not None:
                plan.notes.append(f"#{number}: `{module}` keeps its place: the taxonomy already places it")
            else:
                if title is None:
                    title = (inherited[module][1] if module in inherited and inherited[module][0] == to
                             else default_title(head, module))
                numbers = asked.setdefault(module, {}).setdefault((to, title), [])
                if number not in numbers:
                    numbers.append(number)
    chosen: dict[str, Placement] = {}
    for module, spots in sorted(asked.items()):
        if len(spots) == 1:
            (to, title), numbers = next(iter(spots.items()))
            chosen[module] = Placement(module, to, title, ", ".join(f"#{number}" for number in numbers))
        else:
            asking = ", ".join(f"#{number}" for numbers in spots.values() for number in numbers)
            plan.notes.append(f"`{module}` is left unplaced: {asking} ask for different places")
    for module in new:
        if module not in asked and module in inherited:
            to, title, sources = inherited[module]
            chosen[module] = Placement(module, to, title, sources)
        elif module not in asked and module in unsure:
            plan.notes.append(unsure[module])
    for module, item in sorted(chosen.items()):
        elsewhere = sorted(page for page in pages().get(module, ()) if not in_topic(page, item.to, item.title))
        if module in old_modules and subject_of(module, taxonomy) is None:
            plan.notes.append(f"`{module}` is left unplaced: it is older than the batch, in a folder with no subject, so "
                              "the batch would give pages only to its new declarations; placing it is a graph pull "
                              "request that also runs the sync over the whole project")
        elif elsewhere:
            plan.notes.append(f"`{module}` is left unplaced: it already has pages outside the topic `{item.title}` of "
                              f"`{item.to}`, such as `{elsewhere[0]}`, which a placement would not move; placing it is "
                              "a graph pull request that moves them")
        else:
            plan.added.append(item)
    placed = {item.module for item in plan.added}
    plan.unplaced = [(module, subject_of(module, taxonomy)) for module in new if module not in placed]
    changed = {module for path in changed_between(base, head) if (module := library_module(path)) in modules}
    plan.subjectless = sorted(module for module in changed - set(new) - placed
                              if placement_of(module, placements) is None and subject_of(module, taxonomy) is None)
    plan.dropped = sorted(key for key in placements if key.split("/", 1)[0] in wiki.LIBRARIES
                          and key not in modules and key not in folders)
    return plan


def placement_entries(lines: list[str]) -> list[tuple[str, list[str]]]:
    """The entries of the lines of scripts/taxonomy.json's placements block, in order, each as its module and its
    lines without the comma that ends the last of them: one line, as the file writes an entry, or several, as a hand
    edit may leave one. ValueError if the lines are not such entries."""
    entries, number = [], 0
    while number < len(lines):
        if not PLACEMENT_START.match(lines[number]):
            raise ValueError(f"scripts/taxonomy.json: not a placement entry: {lines[number][:80]}")
        for last in range(number, len(lines)):
            if last > number and PLACEMENT_START.match(lines[last]):
                raise ValueError(f"scripts/taxonomy.json: a placement entry does not end before the next one: "
                                 f"{lines[number][:80]}")
            chunk = lines[number:last + 1]
            comma = chunk[-1].endswith(",")
            text = "\n".join(chunk)[:-1] if comma else "\n".join(chunk)
            try:
                entry = json.loads("{" + text + "}")
            except ValueError:
                continue
            if len(entry) == 1 and isinstance(next(iter(entry.values())), dict):
                entries.append((next(iter(entry)), chunk[:-1] + [chunk[-1][:-1] if comma else chunk[-1]]))
                number = last + 1
                break
        else:
            raise ValueError(f"scripts/taxonomy.json: a placement entry does not end: {lines[number][:80]}")
    return entries


def edit_placements(text: str, added: dict[str, dict[str, str]], dropped: list[str]) -> str:
    """scripts/taxonomy.json's *text* with the placements *added* and without those *dropped*. Each added entry is one
    line, as the file writes it, right after the entry whose module comes last before its own in plain string order,
    or first if none does: its place depends on the entries, not on when it is added, as insert_rows places a links
    file's rows. A dropped entry loses all its lines, and every other line stays as it is, an entry over several lines
    included. ValueError if the placements block cannot be read entry by entry (placement_entries)."""
    lines = text.split("\n")
    try:
        start = lines.index(' "placements": {')
        end = next(number for number in range(start + 1, len(lines)) if lines[number] in (" }", " },"))
    except (ValueError, StopIteration):
        raise ValueError("scripts/taxonomy.json has no placements block") from None
    entries = placement_entries(lines[start + 1:end])
    keys = {key for key, _ in entries}
    if overlap := sorted(keys & set(added)):
        raise ValueError(f"already placed: {', '.join(overlap)}")
    if missing := sorted(set(dropped) - keys):
        raise ValueError(f"no such placement: {', '.join(missing)}")
    kept = [(key, chunk) for key, chunk in entries if key not in set(dropped)]
    for key, spot in sorted(added.items()):
        line = f"  {json.dumps(key, ensure_ascii=False)}: {json.dumps(spot, ensure_ascii=False)}"
        at = max(((other, number) for number, (other, _) in enumerate(kept) if other < key), default=(None, -1))[1]
        kept.insert(at + 1, (key, [line]))
    block = [line for number, (_, chunk) in enumerate(kept)
             for line in chunk[:-1] + [chunk[-1] + ("," if number < len(kept) - 1 else "")]]
    edited = "\n".join(lines[:start + 1] + block + lines[end:])
    before, after = json.loads(text), json.loads(edited)
    expected = {key: value for key, value in before["placements"].items() if key not in set(dropped)} | added
    if after["placements"] != expected or {**after, "placements": None} != {**before, "placements": None}:
        raise ValueError("editing the placements changed something else")
    return edited


def local_commit(tree: str, parents: list[str], message: str) -> str:
    """A commit of *tree* on *parents*, made only to compare with (LOCAL_IDENTITY)."""
    command = ["git", "-C", str(wiki.ROOT), "commit-tree", tree, *(part for parent in parents for part in ("-p", parent)),
               "-m", message]
    return subprocess.run(command, env={**os.environ, **LOCAL_IDENTITY}, capture_output=True, check=True,
                          text=True).stdout.strip()


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
    return local_commit(tree, [head], f"The tree of {head} with the Lean of {base}")


def run_sync(root: Path, base: str, report: Path, check: bool) -> tuple[int, str]:
    """Run *root*'s copy of `sync_wiki.py declarations --base BASE` (with --check when *check*), its output kept."""
    command = [sys.executable, str(root / "scripts" / "sync_wiki.py"), "declarations", "--base", base,
               "--report", str(report)] + (["--check"] if check else [])
    result = subprocess.run(command, cwd=root, capture_output=True, text=True)
    return result.returncode, result.stdout + result.stderr


def checked_sync(root: Path, base: str, report: Path) -> tuple[dict, str]:
    """Run *root*'s scoped check from *base* (run_sync) and return its report and output. The report must be this
    run's: *report* is removed first, so a run that stops before writing one, as on a git error, is refused rather than
    read from an earlier run; and the exit status must agree with it, 0 in step and 1 not. BatchError otherwise."""
    report.unlink(missing_ok=True)
    status, output = run_sync(root, base, report, check=True)
    try:
        data = json.loads(report.read_text()) if report.is_file() else None
    except ValueError:
        data = None
    if not isinstance(data, dict) or status != (0 if data.get("in_step") is True else 1):
        raise BatchError(f"the scoped check stopped (exit {status}) without a report that agrees with it. Its "
                         "output:\n" + output)
    return data, output


def report_sections(output: str) -> dict[str, list[str]]:
    """The items the sync's printed report lists under each of its sections (sync_wiki.REPORT), by kind."""
    titles = {f"{title}: ": kind for kind, title in sync.REPORT}
    found: dict[str, list[str]] = {}
    current = None
    for line in output.splitlines():
        if line.startswith("  ") and current is not None:
            found[current].append(line[2:])
            continue
        current = next((kind for title, kind in titles.items() if line.startswith(title)
                        and line[len(title):].strip().isdigit()), None)
        if current is not None:
            found.setdefault(current, [])
    return found


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
    return "\n".join([f"{SUBJECT}{head[:12]}", "", textwrap.fill(summary, 72), "", f"{BASE_TRAILER}: {base}",
                      f"{THROUGH_TRAILER}: {head}", ""])


def make(options) -> int:
    head = commit_of("HEAD")
    if left := status_paths():
        raise BatchError(f"make needs a clean checkout of main; it has changes: {', '.join(left[:5])}. Commit or "
                         "remove them, or make the batch in a fresh checkout")
    last = last_batch(head)
    if options.base:
        base = commit_of(options.base)
        if last is not None and not is_ancestor(base, last[2]):
            raise BatchError(f"{base} is after {last[2]}, where the last batch ended: a batch from it would skip the "
                             "Lean merged in between")
    elif last is not None:
        base = last[2]
    else:
        raise BatchError("no batch on this branch yet: give the first batch's base with --base")
    if base == head or base not in mainline(head):
        raise BatchError(f"{base} is not an older commit of this branch's first-parent history")
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
    print(output, end="" if output.endswith("\n") else "\n", flush=True)
    restore = "`git reset --hard` and `git clean -fd blueprint` restore the checkout"
    if status:
        raise BatchError(f"the sync stopped, and nothing is committed; {restore}. When it stops on what main already "
                         "carries, fix that on main first: every batch from here would stop the same way")
    changed = status_paths()
    if stray := [path for path in changed if not batch_path(path)]:
        raise BatchError(f"the run changed files a batch never changes: {', '.join(stray)}; nothing is committed, and "
                         f"{restore}")
    if not changed:
        print("Nothing to sync: the graph is in step with the Lean merged up to here.")
        for note in plan.notes + [f"{module} gets no pages: its folder has no subject" for module in plan.subjectless]:
            print(f"note: {note}")
        return 0
    git("add", "-A", "--", TAXONOMY_PATH, "scripts/wiki-sync.json", "blueprint/roadmap", "blueprint/links")
    git("commit", "-q", "--no-verify", "-F", "-", data=message_for(base, head, plan, report).encode())
    commit = commit_of("HEAD")
    print(f"Committed the batch as {commit}.", flush=True)
    try:
        verify_commit(commit, bodies, plan=plan)
    except BatchError as error:
        raise BatchError(f"{error}\nThe batch does not check: `git reset --hard HEAD^` takes the commit away") from None
    if options.body:
        options.body.write_text(describe(commit, base, head, plan, report, report_sections(output)), encoding="utf-8")
    return 0


@dataclass
class Verdict:
    base: str
    through: str
    plan: PlacementPlan
    # The report and the items for an editor of the sync as make runs it (run_sync, report_sections), when verify
    # recomputes what the batch does; None otherwise.
    made: tuple[dict, dict[str, list[str]]] | None = None


def verify_commit(commit: str, bodies: dict[int, str], plan: PlacementPlan | None = None,
                  onto: str | None = None, recompute: bool = False) -> Verdict:
    """Check that *commit* is a batch on the first-parent history of the checkout's HEAD (batch_of), that it starts no
    later than where the last batch before it ended, and that it is exactly what make writes (see the module
    docstring); and, given a newer main *onto*, that it still merges cleanly into it, with one entry a module in the
    taxonomy, and that the scoped check finds nothing the merge breaks there, such as a second page for a declaration
    or a link to one main no longer has; BatchError otherwise. With *recompute*, also run the sync as make does, on the
    commit the batch was made on, for what the batch does (Verdict.made)."""
    head = commit_of("HEAD")
    found = batch_of(commit, head)
    if found is None:
        raise BatchError(f"{commit} is not a batch of this checkout's main: one commit, with make's message and its "
                         f"{BASE_TRAILER} and {THROUGH_TRAILER} trailers, on the commit the second names, both commits "
                         "on main's first-parent history, that changes only a batch's files. Run verify from an "
                         "up-to-date checkout of main")
    base, through = found
    if (last := last_batch(through)) is not None and not is_ancestor(base, last[2]):
        raise BatchError(f"the batch starts at {base}, after {last[2]}, where the last batch before it ended: it skips "
                         "the Lean merged in between")
    plan = plan or placement_plan(base, through, bodies)
    expected = edit_placements(blob(through, TAXONOMY_PATH).decode("utf-8"), plan.entries(), plan.dropped)
    actual = (blob(commit, TAXONOMY_PATH) or b"").decode("utf-8")
    if expected != actual:
        try:
            want, have = json.loads(expected)["placements"], json.loads(actual)["placements"]
            differ = sorted(key for key in want.keys() | have.keys() if want.get(key) != have.get(key))
        except (ValueError, KeyError, TypeError):
            differ = []
        raise BatchError("the batch's scripts/taxonomy.json is not main's with the placement plan applied: "
                         + (f"the entries of {', '.join(differ[:10])} differ" if differ else "its bytes differ")
                         + ". If a merged pull request's description changed since make read it, make a new batch")
    taxonomy = git("rev-parse", f"{commit}:{TAXONOMY_PATH}").decode().strip()
    synthetic = synthetic_base(base, through, taxonomy)
    merged = None
    if onto is not None:
        result = subprocess.run(["git", "-C", str(wiki.ROOT), "merge-tree", "--write-tree", "--no-messages", onto,
                                 commit], capture_output=True, text=True)
        if result.returncode:
            raise BatchError(f"the batch no longer merges cleanly into {onto}: make a new batch from a fresh main")
        tree = result.stdout.split()[0]
        try:
            sync.STRICT_JSON.decode(git("cat-file", "blob", f"{tree}:{TAXONOMY_PATH}").decode("utf-8"))
        except ValueError as error:
            raise BatchError(f"merged into {onto}, the batch leaves scripts/taxonomy.json unreadable ({error}): make a "
                             "new batch from a fresh main") from None
        merged = local_commit(tree, [onto, commit], f"The batch {commit} merged into {onto}")
    with tempfile.TemporaryDirectory(prefix="atlas-batch-verify-") as folder:
        tree = Path(folder) / "tree"
        git("worktree", "add", "-q", "--detach", str(tree), commit)
        try:
            report, output = checked_sync(tree, synthetic, Path(folder) / "batch-report.json")
            if report.get("in_step") is not True or report.get("wiki_changes") not in ("sync", "none"):
                raise BatchError("the scoped check does not find the batch's wiki exactly the sync's, in step. Its "
                                 "output:\n" + output)
            if merged is not None:
                subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--detach", merged], check=True,
                               capture_output=True)
                try:
                    onto_report, output = checked_sync(tree, onto, Path(folder) / "merge-report.json")
                except BatchError as error:
                    raise BatchError(f"merged into {onto}, the batch could not be checked: {error}") from None
                if onto_report.get("in_step") is not True:
                    raise BatchError(f"merged into {onto}, the batch breaks what the scoped check reads: make a new "
                                     "batch from a fresh main. Its output:\n" + output)
            made = None
            if recompute:
                subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--detach", through], check=True,
                               capture_output=True)
                (tree / TAXONOMY_PATH).write_bytes(git("cat-file", "blob", f"{commit}:{TAXONOMY_PATH}"))
                made_path = Path(folder) / "made-report.json"
                status, output = run_sync(tree, synthetic, made_path, check=False)
                if status or not made_path.is_file():
                    raise BatchError(f"running the sync as make does stopped (exit {status}). Its output:\n" + output)
                made = (json.loads(made_path.read_text()), report_sections(output))
        finally:
            git("worktree", "remove", "--force", str(tree))
    print(f"{commit} is the batch from {base} up to {through}: its taxonomy is main's with the placement plan "
          "applied, and its wiki is in step, exactly what the sync writes."
          + (f" It merges cleanly into {onto}, and the scoped check finds nothing the merge breaks." if onto else ""))
    return Verdict(base, through, plan, made)


def describe(commit: str, base: str, head: str, plan: PlacementPlan, report: dict,
             sections: dict[str, list[str]]) -> str:
    """A description for the batch's pull request, in Markdown. Every value in it is the repository's, or a
    description's line that parse_place checked."""
    missing = report.get("missing", [])
    modules: dict[str, int] = {}
    for key in missing:
        modules[report["new"][key]] = modules.get(report["new"][key], 0) + 1
    folders = sum(1 for path in changed_between(head, commit)
                  if path.startswith("blueprint/roadmap/") and path.endswith("/README.md"))
    digests = report.get("digests", {})
    recorded = sum(1 for value in digests.values() if value is not None)
    unrecorded = [page for page in report.get("changed", []) if page.split(" (", 1)[0] in digests]
    lines = ["Graph: batch", "",
             f"Pages for the documented declarations that the Lean merged into `main` after `{base}`, up to `{head}`, "
             "left without one, made by `scripts/graph_batch.py make` "
             "([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)).", "",
             f"- {len(missing)} new pages, for declarations of {len(modules)} modules; {folders} folder pages written "
             f"or extended; {recorded} docstring digests written and {len(digests) - recorded} dropped.",
             f"- {len(plan.added)} modules placed in `scripts/taxonomy.json`, {len(plan.dropped)} placements of modules "
             "that no longer exist dropped.", ""]
    if plan.added:
        lines += ["### Placements", "", "| Module | Field | Topic | From |", "| --- | --- | --- | --- |"]
        lines += [f"| `{item.module}` | `{item.to}` | `{item.title}` | {item.source} |" for item in plan.added]
        lines.append("")
    if plan.dropped:
        lines += ["### Placements dropped", ""] + [f"- `{key}`" for key in plan.dropped] + [""]
    if plan.unplaced:
        lines += ["### New modules left unplaced", "", "Nothing placed them: they had no `Place:` line and took no placed "
                  "module's declarations, or the notes below say why not. Placing one is a graph pull request that "
                  "moves its pages; for one with no pages, in a folder with no subject, it also runs the whole-project "
                  "sync, which writes them ([Maintaining articles](docs/BLUEPRINT.md#maintaining-articles)):", ""]
        lines += [f"- `{module}`: " + (f"in `{subject}/not-yet-classified/`" if subject else
                                       "**no pages**, as its folder has no subject")
                  for module, subject in plan.unplaced]
        lines.append("")
    if plan.subjectless:
        lines += ["### Changed modules with no pages", "", "Their folders have no subject, so their new documented "
                  "declarations get no pages until a graph pull request places them and runs the whole-project sync:",
                  ""] + [f"- `{module}`" for module in plan.subjectless] + [""]
    if plan.notes:
        lines += ["### Left for an editor", ""] + [f"- {note}" for note in plan.notes] + [""]
    for kind, title in sync.REPORT:
        if kind in EDITOR_ITEMS and sections.get(kind):
            lines += [f"### {title}", "", "```text"] + sections[kind] + ["```", ""]
    if unrecorded:
        lines += ["### Pages to check", "", "Their declaration's docstring changed, and no pull request recorded the "
                  "new digest:", "", "```text"] + unrecorded + ["```", ""]
    for title, key in (("Held back, so with no page", "held"), ("Listed as duplicates, so with no page", "duplicates")):
        if report.get(key):
            lines += [f"### {title}", "", "```text"] + report[key] + ["```", ""]
    lines += ["### New pages by module", ""] + [f"- `{module}`: {count}" for module, count in sorted(modules.items())]
    lines += ["", "## Validation", "",
              f"- `python3 scripts/graph_batch.py verify {commit}`, from a checkout of `main` that has `{head}`: the "
              "taxonomy is main's with the placement plan applied, and the scoped check finds the wiki in step, "
              "exactly what the sync writes."]
    return "\n".join(lines) + "\n"


def run_verify(options) -> int:
    commit = commit_of(options.commit)
    head = commit_of("HEAD")
    if head == commit:
        raise BatchError("run verify from an up-to-date checkout of main, not from the batch itself: its checks are "
                         "against main's history, and they run this checkout's copy of the scripts")
    found = batch_of(commit, head)
    if found is None:
        raise BatchError(f"{commit} is not a batch of this checkout's main: one commit, with make's message and its "
                         f"{BASE_TRAILER} and {THROUGH_TRAILER} trailers, on the commit the second names, both commits "
                         "on main's first-parent history, that changes only a batch's files. Run verify from an "
                         "up-to-date checkout of main")
    # From a newer main, the batch must still merge into it as it is.
    onto = head if head not in (commit, found[1]) and not is_ancestor(head, commit) else None
    verdict = verify_commit(commit, bodies_for(*found, options.bodies), onto=onto, recompute=True)
    # What the reviewer reads: recomputed here, not taken from the pull request's description, which can be edited.
    report, sections = verdict.made
    text = describe(commit, verdict.base, verdict.through, verdict.plan, report, sections)
    print("\nWhat the batch does, as verify recomputes it from main (read this, not the pull request's "
          "description):\n")
    print(text)
    if options.body:
        options.body.write_text(text, encoding="utf-8")
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
    making.add_argument("--base", metavar="REV", help="where the batch starts: the first batch's base, or an earlier "
                                                      "commit than where the last batch ended")
    making.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    making.add_argument("--body", type=Path, metavar="FILE",
                        help="write a description for the pull request, outside the checkout")
    verifying = commands.add_parser("verify", help="check that a commit is exactly the batch make writes")
    verifying.add_argument("commit", metavar="REV", help="the batch's head commit")
    verifying.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    verifying.add_argument("--body", type=Path, metavar="FILE",
                           help="also write the description verify recomputes, outside the checkout")
    basing = commands.add_parser("base", help="print the last batch and where the next one starts")
    basing.add_argument("rev", nargs="?", default="HEAD", metavar="REV")
    options = parser.parse_args(argv)
    try:
        return {"make": make, "verify": run_verify, "base": run_base}[options.command](options)
    except (BatchError, sync.GitError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        stderr = error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else error.stderr or ""
        print(f"error: {' '.join(map(str, error.cmd))} failed: {stderr.strip()}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
